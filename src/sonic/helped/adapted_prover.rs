use crate::pairing::ff::{Field};
use crate::pairing::{Engine, CurveProjective};
use std::marker::PhantomData;

use super::{Proof, SxyAdvice};
use super::batch::Batch;
use super::poly::{SxEval, SyEval};
use super::parameters::{Parameters};

use crate::SynthesisError;

use crate::sonic::transcript::{Transcript, TranscriptProtocol};
use crate::sonic::util::*;
use crate::sonic::cs::{Backend, SynthesisDriver};
use crate::{Circuit};
use crate::sonic::sonic::AdaptorCircuit;
use crate::sonic::srs::SRS;
use crate::sonic::sonic::Basic;
use super::prover::create_advice as create_advice_sonic_circuit;
use super::prover::create_advice_on_information_and_srs as create_advice_on_information_and_srs_sonic_circuit;
use super::prover::create_proof_on_srs as create_proof_on_srs_sonic_circuit;
use crate::sonic::sonic::CountN;

// pub fn create_advice_on_information_and_srs<E: Engine, C: Circuit<E> + Clone, S: SynthesisDriver>(
pub fn create_advice_on_information_and_srs<E: Engine, C: Circuit<E> + Clone>(
    circuit: C,
    proof: &Proof<E>,
    srs: &SRS<E>,
    n: usize
) -> Result<SxyAdvice<E>, SynthesisError>
{
    let adapted_circuit = AdaptorCircuit(circuit);

    create_advice_on_information_and_srs_sonic_circuit::<_, _, Basic>(&adapted_circuit, proof, srs, n)
}

// pub fn create_advice<E: Engine, C: Circuit<E> + Clone, S: SynthesisDriver>(
pub fn create_advice<E: Engine, C: Circuit<E> + Clone>(
    circuit: C,
    proof: &Proof<E>,
    parameters: &Parameters<E>,
) -> Result<SxyAdvice<E>, SynthesisError>
{
    let n = parameters.vk.n;
    create_advice_on_information_and_srs::<E, C>(circuit, proof, &parameters.srs, n)   
}

// pub fn create_advice_on_srs<E: Engine, C: Circuit<E> + Clone, S: SynthesisDriver>(
pub fn create_advice_on_srs<E: Engine, C: Circuit<E> + Clone>(
    circuit: C,
    proof: &Proof<E>,
    srs: &SRS<E>
) -> Result<SxyAdvice<E>, SynthesisError>
{
    use crate::sonic::sonic::Nonassigning;

    let adapted_circuit = AdaptorCircuit(circuit.clone());
    // annoying, but we need n to compute s(z, y), and this isn't
    // precomputed anywhere yet
    let n = {
        let mut tmp = CountN::<Nonassigning>::new();
        Nonassigning::synthesize(&mut tmp, &adapted_circuit)?;

        tmp.n
    };

    create_advice_on_information_and_srs::<E, C>(circuit, proof, srs, n)   
}

// pub fn create_proof<E: Engine, C: Circuit<E> + Clone, S: SynthesisDriver>(
pub fn create_proof<E: Engine, C: Circuit<E> + Clone>(
    circuit: C,
    parameters: &Parameters<E>
) -> Result<Proof<E>, SynthesisError> {
    create_proof_on_srs::<E, C>(circuit, &parameters.srs)
}

// pub fn create_proof_on_srs<E: Engine, C: Circuit<E> + Clone, S: SynthesisDriver>(
pub fn create_proof_on_srs<E: Engine, C: Circuit<E> + Clone>(
    circuit: C,
    srs: &SRS<E>
) -> Result<Proof<E>, SynthesisError>
{
    let adapted_circuit = AdaptorCircuit(circuit);

    create_proof_on_srs_sonic_circuit::<_, _, Basic>(&adapted_circuit, srs)
}

// #[test]
// fn my_fun_circuit_test() {
//     use crate::pairing::ff::PrimeField;
//     use crate::pairing::bls12_381::{Bls12, Fr};
//     use super::*;
//     use crate::sonic::cs::{Basic, ConstraintSystem, LinearCombination};

//     struct MyCircuit;

//     impl<E: Engine> Circuit<E> for MyCircuit {
//         fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
//             let (a, b, _) = cs.multiply(|| {
//                 Ok((
//                     E::Fr::from_str("10").unwrap(),
//                     E::Fr::from_str("20").unwrap(),
//                     E::Fr::from_str("200").unwrap(),
//                 ))
//             })?;

//             cs.enforce_zero(LinearCombination::from(a) + a - b);

//             //let multiplier = cs.alloc_input(|| Ok(E::Fr::from_str("20").unwrap()))?;

//             //cs.enforce_zero(LinearCombination::from(b) - multiplier);

//             Ok(())
//         }
//     }

//     let srs = SRS::<Bls12>::new(
//         20,
//         Fr::from_str("22222").unwrap(),
//         Fr::from_str("33333333").unwrap(),
//     );
//     let proof = create_proof_on_srs::<Bls12, _, Basic>(&MyCircuit, &srs).unwrap();

//     use std::time::{Instant};
//     let start = Instant::now();
//     let mut batch = MultiVerifier::<Bls12, _, Basic>::new(MyCircuit, &srs).unwrap();

//     for _ in 0..1 {
//         batch.add_proof(&proof, &[/*Fr::from_str("20").unwrap()*/], |_, _| None);
//     }

//     assert!(batch.check_all());

//     let elapsed = start.elapsed();
//     println!("time to verify: {:?}", elapsed);
// }
