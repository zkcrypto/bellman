//! Implementation of a duplex sponge construction based on the Rescue algebraic
//! permutation.
//! copied from Halo implementation
//! 
//! NB: current implementation works only with base fields of length 256 bits = 8 limbs

use crate::ff::{PrimeField, PrimeFieldRepr};
use num::integer::*;
use num::bigint::{BigUint};
use num::{Zero, One};
use num::ToPrimitive;

use tiny_keccak::Keccak;

// 
trait RescueParams<F: PrimeField> {
    
    fn default() -> Self;
    fn get_num_rescue_rounds(&self) -> usize;
    // r = SPONGE_RATE and t = RESCUE_M = r + c
    fn c(&self) -> usize;
    fn r(&self) -> usize;
    fn t(&self) -> usize;
    fn get_mds_matrix(&self) -> &Vec<Vec<F>>;
    fn get_key_schedule(&self) -> &Vec<Vec<F>>;
    // TODO: Decide on a padding strategy (currently padding with answer for the main qestion of the universe)
    fn padding_constant(&self) -> &F;

    // p - 1 is divisible by 2^s and not divisible by 2^(s+1)
    fn s(&self) -> u32;
    /// Generator of the 2^s multiplicative subgroup
    fn alpha(&self) -> &F;
    /// Ideally the smallest prime such that gcd(p - 1, alpha) = 1
    fn rescue_alpha(&self) -> u64;
    /// RESCUE_INVALPHA * RESCUE_ALPHA = 1 mod (p - 1)
    fn rescue_invalpha(&self) -> &[u64; 4];
    /// Element of multiplicative order 3.
    fn beta(&self) -> &F;

    // TODO: generate all the parameters from intialization vector and parameters 
    // fn new(&str, c, r, num_of_rounds) -> Self
}

fn mds<F: PrimeField, Params: RescueParams<F>>(
    in_state: &[F],
    params: &Params,
) -> Vec<F> {
    let mut out_state = vec![];
    let mds_matrix = params.get_mds_matrix();
    let RESCUE_M = params.t();
    
    for i in 0..RESCUE_M {
        let mut res = F::zero();
        for j in 0..RESCUE_M {
            let mut temp = mds_matrix[i][j].clone();
            temp.mul_assign(&in_state[j]);
            res.add_assign(&temp);
        }
        out_state.push(res);
    }
    out_state
}


fn rescue_f<F: PrimeField, Params: RescueParams<F>>(
    state: &mut [F],
    params: &Params,
) {

    let mds_matrix = params.get_mds_matrix();
    let key_schedule = params.get_key_schedule();
    let RESCUE_M = params.t();
    let RESCUE_ROUNDS = params.get_num_rescue_rounds();
   
    for i in 0..RESCUE_M {
        state[i].add_assign(&key_schedule[0][i]);
    }

    for r in 0..2 * RESCUE_ROUNDS {
        let exp = if r % 2 == 0 {
            params.rescue_invalpha()
        } else {
            &[params.rescue_alpha(), 0, 0, 0]
        };
        for entry in state.iter_mut() {
            *entry = entry.pow(exp);
        }
        for (input, output) in  mds(state, params).iter().zip(state.iter()) {
            *output = *input;
        }
        for i in 0..RESCUE_M {
            state[i].add_assign(&(key_schedule[r + 1][i]));
        }
    }
}

fn pad<F: PrimeField, Params: RescueParams<F>>(
    input: &mut Vec<F>,
    params: &Params,
) {

    let SPONGE_RATE = params.r();
    let magic_constant = params.padding_constant();
    let range = SPONGE_RATE - input.len();

    // apply necessary padding
    input.extend((0..range).map(|_| magic_constant.clone())); 
}

fn rescue_duplex<F: PrimeField, Params: RescueParams<F>>(
    state: &mut Vec<F>,
    input: &mut Vec<F>,
    params: &Params,
) -> Vec<Option<F>> {

    let SPONGE_RATE = params.r();
    pad(&mut input, params);

    for i in 0..SPONGE_RATE {
        state[i].add_assign(&input[i]);
    }

    rescue_f(state, params);

    let mut output = vec![];
    for i in 0..SPONGE_RATE {
        output[i] = Some(state[i]);
    }
    output
}

enum SpongeState<F: PrimeField> {
    Absorbing(Vec<F>),
    Squeezing(Vec<Option<F>>),
}

impl<F: PrimeField> SpongeState<F> {
    fn absorb(val: F, SPONGE_RATE: usize) -> Self {
        SpongeState::Absorbing(vec![val])
    }
}

pub struct Rescue<F: PrimeField, RP: RescueParams<F>> {
    sponge: SpongeState<F>,
    state: Vec<F>,
    _marker: std::marker::PhantomData<RP>,
}

impl<F: PrimeField, RP: RescueParams<F>> Rescue<F, RP> {
    //we use master key as a parameter here
    pub fn new(params: &RP) -> Self {
        
        let RESCUE_M = params.t();
        let SPONGE_STATE = params.r();
        let state = (0..RESCUE_M).map(|_| F::zero()).collect();

        Rescue {
            sponge: SpongeState::Absorbing(vec![]),
            state,
            _marker: std::marker::PhantomData::<RP>,
        }
    }

    pub fn absorb(&mut self, val: F, params: &RP) {
        let SPONGE_STATE = params.r();
        match self.sponge {
            SpongeState::Absorbing(ref mut input) => {
                if input.len() < SPONGE_STATE {
                    input.push(val);
                    return;
                }

                // We've already absorbed as many elements as we can
                let _ = rescue_duplex(&mut self.state, input, params);
                self.sponge = SpongeState::absorb(val, SPONGE_STATE);
            }
            SpongeState::Squeezing(_) => {
                // Drop the remaining output elements
                self.sponge = SpongeState::absorb(val, SPONGE_STATE);
            }
        }
    }

    pub fn squeeze(&mut self, params: &RP) -> F {
        loop {
            match self.sponge {
                SpongeState::Absorbing(input) => {
                    self.sponge = SpongeState::Squeezing(rescue_duplex(
                        &mut self.state,
                        &input,
                        &self.mds_matrix,
                        &self.key_schedule,
                        &self.params
                    ));
                }
                SpongeState::Squeezing(ref mut output) => {
                    for entry in output.iter_mut() {
                        if let Some(e) = entry.take() {
                            return e;
                        }
                    }
                    // We've already squeezed out all available elements
                    unreachable!("Sponge number is too small");
                    //self.sponge = SpongeState::Absorbing([None; SPONGE_RATE]);
                }
            }
        }
    }
}