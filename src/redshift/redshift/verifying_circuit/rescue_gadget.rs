use crate::pairing::ff::{Field, PrimeField, PrimeFieldRepr};
use crate::pairing::{Engine};
use super::common::*;
use crate::cs::*;

use crate::redshift::IOP::hashes::rescue::{RescueParams};
use tiny_keccak::Keccak;


pub(crate) const RESCUE_ROUNDS: usize = 22;
pub(crate) const RESCUE_M: usize = 2;

// Set sponge capacity to 11
pub(crate) const SPONGE_RATE: usize = 1;
pub(crate) const RESCUE_CONST_IV: &str = "qwerty";


pub(crate) fn generate_mds_matrix<F: PrimeField>(_params: &RescueParams<F>) -> [[F; RESCUE_M]; RESCUE_M] {
    // TODO: Correct MDS generation; this causes horribly-biased output
    // in order to simplify output - the first index is column, the second is row
    let mut mds_matrix = [[F::zero(); RESCUE_M]; RESCUE_M * 2];
    for i in 0..RESCUE_M {
        for j in 0..(RESCUE_M * 2) {
            mds_matrix[j][i] = F::multiplicative_generator().pow([(i*j) as u64]);
        }
    }

    fn swap_rows<F: PrimeField>(matrix: &mut[[F; RESCUE_M]; RESCUE_M * 2], i: usize, j: usize ) -> () {
        if i == j {
            return;
        }

        for k in 0..(RESCUE_M * 2) {
            let temp = matrix[k][i];
            matrix[k][i] = matrix[k][j];
            matrix[k][j] = temp;
        }
    }

    //convert the resulting matrix to echelon_form
    for i in 0..RESCUE_M {
        let opt_idx = (i..RESCUE_M).find(|&k| ! mds_matrix[i][k].is_zero());
        if let Some(idx) = opt_idx {
            swap_rows(&mut mds_matrix, i, idx);
            let elem_inv = mds_matrix[i][idx].inverse().expect("should be non-zero");

            for j in (i+1)..RESCUE_M {
                let mut coef = mds_matrix[i][j];
                coef.mul_assign(&elem_inv);
                mds_matrix[i][j] = F::zero();

                for k in (i+1)..(RESCUE_M * 2) {
                    let mut temp = mds_matrix[k][idx].clone();
                    temp.mul_assign(&coef);
                    mds_matrix[k][j].sub_assign(&temp);
                }
            }
        }
    }

    //now we need to return the right half of the matrix
    let mut res = [[F::zero(); RESCUE_M]; RESCUE_M];
    res.clone_from_slice(&mds_matrix[RESCUE_M..]);
    res
}


fn rescue_f<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    state: &mut [Combination<E>; RESCUE_M],
    mds_matrix: &[[E::Fr; RESCUE_M]; RESCUE_M],
    key_schedule: &[[Num<E>; RESCUE_M]; 2 * RESCUE_ROUNDS + 1],
    params: &Params<E>,
) -> Result<(), SynthesisError> {
    for (entry, key) in state.iter_mut().zip(key_schedule[0].iter()) {
        entry.add_assign_num(key);
    }

    for r in 0..2 * RESCUE_ROUNDS {
        let mut mid = vec![];
        for entry in state.iter() {
            if r % 2 == 0 {
                mid.push(
                    entry.rescue_invalpha(&mut cs.namespace(|| format!("round {} s-box 1", r / 2)), params)?,
                );
            } else {
                mid.push(entry.rescue_alpha(&mut cs.namespace(|| format!("round {} s-box 2", r / 2)), params)?);
            };
        }

        for (next_entry, (mds_row, key)) in state
            .iter_mut()
            .zip(mds_matrix.iter().zip(key_schedule[r + 1].iter()))
        {
            let mut sum = Combination::from(Num::constant(E::Fr::zero()));
            for (coeff, entry) in mds_row.iter().zip(mid.iter()) {
                let temp = entry.scale(*coeff);
                sum.add_assign_num(&temp);
            }
            sum.add_assign_num(key);
            *next_entry = sum;
        }
    }

    Ok(())
}

fn generate_constants<E: Engine>(iv: &str) -> [[Num<E>; RESCUE_M]; 2 * RESCUE_ROUNDS + 1] {

    let mut hasher = Keccak::new_shake256();
    hasher.update(iv.as_bytes());
    let REPR_SIZE: usize = (((E::Fr::NUM_BITS as usize)/ 64) + 1) * 8;
    let mut buf = Vec::with_capacity(REPR_SIZE);
    let temp : [Num<E>; RESCUE_M] = array_init::array_init(|_: usize| Num::zero());
    let mut res : [[Num<E>; RESCUE_M]; 2 * RESCUE_ROUNDS + 1] = array_init::array_init(|_: usize| temp.clone());
    for i in 0..RESCUE_M {
        for j in 0..(2*RESCUE_ROUNDS +1) {

            hasher.squeeze(&mut buf[..]);
            let mut repr = <E::Fr as PrimeField>::Repr::default();
            //repr.read_be(&buf[..]).expect("will read");
            //res[i][j] = Num::constant(E::Fr::from_repr(repr).unwrap());
            res[j][i] = Num::zero();
        }
    }
    
    res
}

/// Duplicates [`rescue_f`] in order to extract the key schedule.
fn generate_key_schedule<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    master_key: [Num<E>; RESCUE_M],
    mds_matrix: &[[E::Fr; RESCUE_M]; RESCUE_M],
    params: &Params<E>,
) -> Result<[[Num<E>; RESCUE_M]; 2 * RESCUE_ROUNDS + 1], SynthesisError> 
{

    fn simplify_arr<E: Engine, CS: ConstraintSystem<E>>(arr: &mut [Combination<E>; RESCUE_M], cs: &mut CS) -> 
        Result<[Num<E>; RESCUE_M], SynthesisError> {
        let mut res : [Num<E>; RESCUE_M] = array_init::array_init(|_: usize| Num::zero());
        for (elem, out) in arr.iter_mut().zip(res.iter_mut()) {
            *out = elem.simplify(cs)?;
        }
        Ok(res)
    }
    let constants = generate_constants(RESCUE_CONST_IV);

    let mut key_schedule = [[Num::zero(); RESCUE_M]; 2 * RESCUE_ROUNDS + 1];
    let mut key_arr_pos = 0;
    let mut state : [Combination<E>; RESCUE_M] = array_init::array_init(|_: usize| Combination::zero());

    for i in 0..RESCUE_M {
        state[i].add_assign_num(&master_key[i]);
        state[i].add_assign_num(&constants[0][i]);
    }
    key_schedule[key_arr_pos] = simplify_arr(&mut state, cs)?;
    key_arr_pos += 1;

    for r in 0..2 * RESCUE_ROUNDS {
        let mut mid = vec![];
        for entry in state.iter() {
            if r % 2 == 0 {
                mid.push(
                    entry.rescue_invalpha(&mut cs.namespace(|| format!("round {} s-box 1", r / 2)), params)?,
                );
            } else {
                mid.push(entry.rescue_alpha(&mut cs.namespace(|| format!("round {} s-box 2", r / 2)), params)?);
            };
        }

        for (next_entry, (mds_row, key)) in state
            .iter_mut()
            .zip(mds_matrix.iter().zip(constants[r + 1].iter()))
        {
            let mut sum = Combination::from(Num::constant(E::Fr::zero()));
            for (coeff, entry) in mds_row.iter().zip(mid.iter()) {
                let temp = entry.scale(*coeff);
                sum.add_assign_num(&temp);
            }
            sum.add_assign_num(key);
            *next_entry = sum;
        }
        
        key_schedule[key_arr_pos] = simplify_arr(&mut state, cs)?;
        key_arr_pos += 1;
    }

    Ok(key_schedule)
}

fn pad<E: Engine, CS: ConstraintSystem<E>>(
    _cs: &mut CS,
    input: &[Option<Num<E>>; SPONGE_RATE],
) -> Result<[Num<E>; SPONGE_RATE], SynthesisError> {
    
    let one = Num::one();
    let mut padded = vec![];
    for i in 0..SPONGE_RATE {
        if let Some(e) = input[i].clone() {
            padded.push(e);
        } else {
            // No more elements; apply necessary padding
            // TODO: Decide on a padding strategy (currently padding with all-ones)
            padded.push(one.clone());
        }
    }

    // Manually expand so that we return a fixed-length array without having to
    // allocate placeholder variables.
    Ok([
        padded[0]
    ])
}

fn rescue_duplex<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    state: &mut [Combination<E>; RESCUE_M],
    input: &[Option<Num<E>>; SPONGE_RATE],
    mds_matrix: &[[E::Fr; RESCUE_M]; RESCUE_M],
    key_schedule: &[[Num<E>; RESCUE_M]; 2 * RESCUE_ROUNDS + 1],
    params: &Params<E>,
) -> Result<(), SynthesisError> {
    for (entry, input) in state
        .iter_mut()
        .zip(pad(&mut cs.namespace(|| "pad input"), input)?.iter())
    {
        entry.add_assign_num(input);
    }

    rescue_f(cs, state, mds_matrix, key_schedule, params)?;

    Ok(())
}

enum SpongeState<E: Engine> {
    Absorbing([Option<Num<E>>; SPONGE_RATE]),
    Squeezing([bool; SPONGE_RATE]),
}

impl<E: Engine> SpongeState<E> {
    fn absorb(val: Num<E>) -> Self {
        let mut input : [Option<Num<E>>; SPONGE_RATE] = array_init::array_init(|_: usize| None);
        input[0] = Some(val);
        SpongeState::Absorbing(input)
    }
}

pub struct RescueGadget<E: Engine> {
    sponge: SpongeState<E>,
    state: [Combination<E>; RESCUE_M],
    mds_matrix: [[E::Fr; RESCUE_M]; RESCUE_M],
    key_schedule: [[Num<E>; RESCUE_M]; 2 * RESCUE_ROUNDS + 1],
    pub params: Params<E>,
}

impl<E: Engine> RescueGadget<E> {
    pub fn new<CS: ConstraintSystem<E>>(cs: &mut CS) -> Result<Self, SynthesisError> {
        let state = [
            Num::constant(E::Fr::zero()).into(),
            Num::constant(E::Fr::zero()).into(),
        ];
        let rescue_params = RescueParams::new();
        let mds_matrix = generate_mds_matrix(&rescue_params);
        let params = Params{ rescue_params};

        // To use Rescue as a permutation, fix the master key to zero
        let temp : [Num<E>; RESCUE_M] = array_init::array_init(|_: usize| Num::zero());
        let key_schedule =
            generate_key_schedule(cs, temp, &mds_matrix, &params)?;

        let input : [Option<Num<E>>; SPONGE_RATE] = array_init::array_init(|_: usize| None);
        Ok(RescueGadget {
            sponge: SpongeState::Absorbing(input),
            state,
            mds_matrix,
            key_schedule,
            params,
        })
    }

    pub fn absorb<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
        val: Num<E>,
    ) -> Result<(), SynthesisError> {
        match self.sponge {
            SpongeState::Absorbing(ref mut input) => {
                for entry in input.iter_mut() {
                    if entry.is_none() {
                        *entry = Some(val);
                        return Ok(());
                    }
                }

                // We've already absorbed as many elements as we can
                rescue_duplex(
                    cs,
                    &mut self.state,
                    input,
                    &self.mds_matrix,
                    &self.key_schedule,
                    &self.params,
                )?;
                self.sponge = SpongeState::absorb(val);
            }
            SpongeState::Squeezing(_) => {
                // Drop the remaining output elements
                self.sponge = SpongeState::absorb(val);
            }
        }

        Ok(())
    }

    pub fn squeeze<CS: ConstraintSystem<E>>(
        &mut self,
        cs: &mut CS,
    ) -> Result<Num<E>, SynthesisError> {
        loop {
            match self.sponge {
                SpongeState::Absorbing(input) => {
                    rescue_duplex(
                        &mut cs.namespace(|| "rescue"),
                        &mut self.state,
                        &input,
                        &self.mds_matrix,
                        &self.key_schedule,
                        &self.params,
                    )?;
                    self.sponge = SpongeState::Squeezing([false; SPONGE_RATE]);
                }
                SpongeState::Squeezing(ref mut output) => {
                    for (squeezed, entry) in output.iter_mut().zip(self.state.iter_mut()) {
                        if !*squeezed {
                            *squeezed = true;

                            let out = entry.simplify(cs); 
                            return out;
                        }
                    }

                    // We've already squeezed out all available elements
                    let input : [Option<Num<E>>; SPONGE_RATE] = array_init::array_init(|_: usize| None);
                    self.sponge = SpongeState::Absorbing(input);
                }
            }
        }
    }
}





