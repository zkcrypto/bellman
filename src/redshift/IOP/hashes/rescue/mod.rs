//! Implementation of a duplex sponge construction based on the Rescue algebraic
//! permutation.
//! copied from Halo implementation
//! 
//! NB: current implementation works only with base fields of length 256 bits = 8 limbs

use crate::ff::{PrimeField, PrimeFieldRepr};
use num::integer::*;
use num::bigint::BigUint;
use num::{Zero, One};
use num::ToPrimitive;

pub(crate) const RESCUE_ROUNDS: usize = 10;
pub(crate) const RESCUE_M: usize = 13;

// Set sponge capacity to 1
pub(crate) const SPONGE_RATE: usize = RESCUE_M - 1;

#[derive(Debug, Copy, Clone)]
pub(crate) struct RescueParams<F>
where F: PrimeField
{
    // p - 1 is divisible by 2^s
    pub S: u32,
    /// Generator of the 2^s multiplicative subgroup
    pub ALPHA: F,
    /// Ideally the smallest prime such that gcd(p - 1, alpha) = 1
    pub RESCUE_ALPHA: u64,
    /// RESCUE_INVALPHA * RESCUE_ALPHA = 1 mod (p - 1)
    pub RESCUE_INVALPHA: [u64; 4],
    /// Element of multiplicative order 3.
    pub BETA: F,
}

impl<F: PrimeField> RescueParams<F>
{
    pub fn new() -> Self {
        let S = F::S;
        let g = F::multiplicative_generator();

        let mut t = F::char();
        t.shr(S);
        let ALPHA = g.pow(t);

        //x inner is equal to p-1
        let mut x_inner = F::char();
        x_inner.div2();
        x_inner.shl(1);

        fn biguint_to_u64_array(mut v: BigUint) -> [u64; 4] {
            let m = BigUint::from(1u64) << 64;
            let mut ret = [0; 4];

            for idx in 0..4 {
                ret[idx] = (&v % &m).to_u64().expect("is guaranteed to fit");
                v >>= 64;
            }
            assert!(v.is_zero());
            ret
        }

        fn compute_alpha_inapha(a: &BigUint) -> (u64, [u64; 4]) {
            let mut alpha = BigUint::from(3u64);
            loop {
                let ExtendedGcd{ gcd, x, y, .. } = a.extended_gcd(&alpha); 
                if gcd.is_one() {
                    let alpha = alpha.to_u64().expect("Should fit in one machine word");
                    let inalpha = biguint_to_u64_array(y);
                    return (alpha, inalpha)
                }
                alpha += BigUint::one();
            }
        }

        let x = BigUint::from(0u64);
        for limb in x_inner.as_ref() {
            x << 64;
            x += BigUint::from(*limb);
        }
        let (RESCUE_ALPHA, RESCUE_INVALPHA) = compute_alpha_inapha(&x);

        let (quotient, remainder) = x.div_rem(&BigUint::from(3u64));
        assert!(remainder.is_zero());
        let BETA = g.pow(&biguint_to_u64_array(quotient));

        RescueParams{ S, ALPHA, RESCUE_ALPHA, RESCUE_INVALPHA, BETA }
    }
}

pub(crate) fn generate_mds_matrix<F: PrimeField>(_params: &RescueParams<F>) -> [[F; RESCUE_M]; RESCUE_M] {
    // TODO: Correct MDS generation; this causes horribly-biased output
    let mut mds_matrix = [[F::zero(); RESCUE_M]; RESCUE_M];
    for i in (0..RESCUE_M).rev() {
        for j in (0..RESCUE_M).rev() {
            let repr = <F::Repr as From<u64>>::from(((i + 1) * j) as u64);
            mds_matrix[i][j] = F::from_repr(repr).unwrap();
        }
    }
    mds_matrix
}

fn mds<F: PrimeField>(
    in_state: &[F; RESCUE_M],
    mds_matrix: &[[F; RESCUE_M]; RESCUE_M],
    _params: &RescueParams<F>
) -> [F; RESCUE_M] {
    let mut out_state = [F::zero(); RESCUE_M];
    for i in 0..RESCUE_M {
        for j in 0..RESCUE_M {
            let mut temp = mds_matrix[i][j].clone();
            temp.mul_assign(&in_state[j]);
            out_state[i].add_assign(&temp);
        }
    }
    out_state
}

fn rescue_f<F: PrimeField>(
    state: &mut [F; RESCUE_M],
    mds_matrix: &[[F; RESCUE_M]; RESCUE_M],
    key_schedule: &[[F; RESCUE_M]; 2 * RESCUE_ROUNDS + 1],
    params: &RescueParams<F>,
) {
    for i in 0..RESCUE_M {
        state[i].add_assign(&key_schedule[0][i]);
    }

    for r in 0..2 * RESCUE_ROUNDS {
        let exp = if r % 2 == 0 {
            params.RESCUE_INVALPHA
        } else {
            [params.RESCUE_ALPHA, 0, 0, 0]
        };
        for entry in state.iter_mut() {
            *entry = entry.pow(&exp);
        }
        *state = mds(state, mds_matrix, params);
        for i in 0..RESCUE_M {
            state[i].add_assign(&(key_schedule[r + 1][i]));
        }
    }
}

/// Duplicates [`rescue_f`] in order to extract the key schedule.
fn generate_key_schedule<F: PrimeField>(
    master_key: [F; RESCUE_M],
    mds_matrix: &[[F; RESCUE_M]; RESCUE_M],
    params: &RescueParams<F>,
) -> [[F; RESCUE_M]; 2 * RESCUE_ROUNDS + 1] {
    // TODO: Generate correct constants
    let constants = [[F::one(); RESCUE_M]; 2 * RESCUE_ROUNDS + 1];

    let mut key_schedule = vec![];
    let mut state = master_key;

    for i in 0..RESCUE_M {
        state[i].add_assign(&(constants[0][i]));
    }
    key_schedule.push(state);

    for r in 0..2 * RESCUE_ROUNDS {
        let exp = if r % 2 == 0 {
            params.RESCUE_INVALPHA
        } else {
            [params.RESCUE_ALPHA, 0, 0, 0]
        };
        for entry in state.iter_mut() {
            *entry = entry.pow(&exp);
        }
        state = mds(&state, mds_matrix, params);
        for i in 0..RESCUE_M {
            state[i].add_assign(&(constants[r + 1][i]));
        }
        key_schedule.push(state);
    }

    [
        key_schedule[0],
        key_schedule[1],
        key_schedule[2],
        key_schedule[3],
        key_schedule[4],
        key_schedule[5],
        key_schedule[6],
        key_schedule[7],
        key_schedule[8],
        key_schedule[9],
        key_schedule[10],
        key_schedule[11],
        key_schedule[12],
        key_schedule[13],
        key_schedule[14],
        key_schedule[15],
        key_schedule[16],
        key_schedule[17],
        key_schedule[18],
        key_schedule[19],
        key_schedule[20],
    ]
}

fn pad<F: PrimeField>(input: &[Option<F>; SPONGE_RATE]) -> [F; SPONGE_RATE] {
    let mut padded = [F::one(); SPONGE_RATE];
    for i in 0..SPONGE_RATE {
        if let Some(e) = input[i] {
            padded[i] = e;
        } else {
            // No more elements; apply necessary padding
            // TODO: Decide on a padding strategy (currently padding with all-ones)
        }
    }
    padded
}

fn rescue_duplex<F: PrimeField>(
    state: &mut [F; RESCUE_M],
    input: &[Option<F>; SPONGE_RATE],
    mds_matrix: &[[F; RESCUE_M]; RESCUE_M],
    key_schedule: &[[F; RESCUE_M]; 2 * RESCUE_ROUNDS + 1],
    params: &RescueParams<F>,
) -> [Option<F>; SPONGE_RATE] {
    let padded = pad(input);
    for i in 0..SPONGE_RATE {
        state[i].add_assign(&padded[i]);
    }

    rescue_f(state, mds_matrix, key_schedule, params);

    let mut output = [None; SPONGE_RATE];
    for i in 0..SPONGE_RATE {
        output[i] = Some(state[i]);
    }
    output
}

#[derive(Clone, Debug)]
enum SpongeState<F: PrimeField> {
    Absorbing([Option<F>; SPONGE_RATE]),
    Squeezing([Option<F>; SPONGE_RATE]),
}

impl<F: PrimeField> SpongeState<F> {
    fn absorb(val: F) -> Self {
        let mut input = [None; SPONGE_RATE];
        input[0] = Some(val);
        SpongeState::Absorbing(input)
    }
}

#[derive(Clone, Debug)]
pub struct Rescue<F: PrimeField> {
    sponge: SpongeState<F>,
    state: [F; RESCUE_M],
    mds_matrix: [[F; RESCUE_M]; RESCUE_M],
    key_schedule: [[F; RESCUE_M]; 2 * RESCUE_ROUNDS + 1],
    params: RescueParams<F>,
}

impl<F: PrimeField> Default for Rescue<F> {
    fn default() -> Self {
        Rescue::new([F::zero(); RESCUE_M])
    }
}

impl<F: PrimeField> Rescue<F> {
    //we use master key as a parameter here
    pub fn new(master_key: [F; RESCUE_M]) -> Self {
        let params = RescueParams::new();
        let mds_matrix = generate_mds_matrix(&params);

        // To use Rescue as a permutation, fix the master key to zero
        let key_schedule = generate_key_schedule(master_key, &mds_matrix, &params);

        Rescue {
            sponge: SpongeState::Absorbing([None; SPONGE_RATE]),
            state: [F::zero(); RESCUE_M],
            mds_matrix,
            key_schedule,
            params,
        }
    }

    pub fn absorb(&mut self, val: F) {
        match self.sponge {
            SpongeState::Absorbing(ref mut input) => {
                for entry in input.iter_mut() {
                    if entry.is_none() {
                        *entry = Some(val);
                        return;
                    }
                }

                // We've already absorbed as many elements as we can
                let _ = rescue_duplex(&mut self.state, input, &self.mds_matrix, &self.key_schedule, &self.params);
                self.sponge = SpongeState::absorb(val);
            }
            SpongeState::Squeezing(_) => {
                // Drop the remaining output elements
                self.sponge = SpongeState::absorb(val);
            }
        }
    }

    pub fn squeeze(&mut self) -> F {
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
                    self.sponge = SpongeState::Absorbing([None; SPONGE_RATE]);
                }
            }
        }
    }
}