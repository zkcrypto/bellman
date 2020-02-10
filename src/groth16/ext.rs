use super::{create_proof_batch_priority, create_random_proof_batch_priority};
use super::{ParameterSource, Proof};
use crate::{Circuit, SynthesisError};
use paired::Engine;
use rand_core::RngCore;

pub fn create_proof<E, C, P: ParameterSource<E>>(
    circuit: C,
    params: P,
    r: E::Fr,
    s: E::Fr,
) -> Result<Proof<E>, SynthesisError>
where
    E: Engine,
    C: Circuit<E> + Send,
{
    let proofs =
        create_proof_batch_priority::<E, C, P>(vec![circuit], params, vec![r], vec![s], false)?;
    Ok(proofs.into_iter().next().unwrap())
}

pub fn create_random_proof<E, C, R, P: ParameterSource<E>>(
    circuit: C,
    params: P,
    rng: &mut R,
) -> Result<Proof<E>, SynthesisError>
where
    E: Engine,
    C: Circuit<E> + Send,
    R: RngCore,
{
    let proofs =
        create_random_proof_batch_priority::<E, C, R, P>(vec![circuit], params, rng, false)?;
    Ok(proofs.into_iter().next().unwrap())
}

pub fn create_proof_batch<E, C, P: ParameterSource<E>>(
    circuits: Vec<C>,
    params: P,
    r: Vec<E::Fr>,
    s: Vec<E::Fr>,
) -> Result<Vec<Proof<E>>, SynthesisError>
where
    E: Engine,
    C: Circuit<E> + Send,
{
    create_proof_batch_priority::<E, C, P>(circuits, params, r, s, false)
}

pub fn create_random_proof_batch<E, C, R, P: ParameterSource<E>>(
    circuits: Vec<C>,
    params: P,
    rng: &mut R,
) -> Result<Vec<Proof<E>>, SynthesisError>
where
    E: Engine,
    C: Circuit<E> + Send,
    R: RngCore,
{
    create_random_proof_batch_priority::<E, C, R, P>(circuits, params, rng, false)
}

pub fn create_proof_in_priority<E, C, P: ParameterSource<E>>(
    circuit: C,
    params: P,
    r: E::Fr,
    s: E::Fr,
) -> Result<Proof<E>, SynthesisError>
where
    E: Engine,
    C: Circuit<E> + Send,
{
    let proofs =
        create_proof_batch_priority::<E, C, P>(vec![circuit], params, vec![r], vec![s], true)?;
    Ok(proofs.into_iter().next().unwrap())
}

pub fn create_random_proof_in_priority<E, C, R, P: ParameterSource<E>>(
    circuit: C,
    params: P,
    rng: &mut R,
) -> Result<Proof<E>, SynthesisError>
where
    E: Engine,
    C: Circuit<E> + Send,
    R: RngCore,
{
    let proofs =
        create_random_proof_batch_priority::<E, C, R, P>(vec![circuit], params, rng, true)?;
    Ok(proofs.into_iter().next().unwrap())
}

pub fn create_proof_batch_in_priority<E, C, P: ParameterSource<E>>(
    circuits: Vec<C>,
    params: P,
    r: Vec<E::Fr>,
    s: Vec<E::Fr>,
) -> Result<Vec<Proof<E>>, SynthesisError>
where
    E: Engine,
    C: Circuit<E> + Send,
{
    create_proof_batch_priority::<E, C, P>(circuits, params, r, s, true)
}

pub fn create_random_proof_batch_in_priority<E, C, R, P: ParameterSource<E>>(
    circuits: Vec<C>,
    params: P,
    rng: &mut R,
) -> Result<Vec<Proof<E>>, SynthesisError>
where
    E: Engine,
    C: Circuit<E> + Send,
    R: RngCore,
{
    create_random_proof_batch_priority::<E, C, R, P>(circuits, params, rng, true)
}
