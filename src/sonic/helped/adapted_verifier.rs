use crate::pairing::ff::{Field};
use crate::pairing::{Engine, CurveProjective};
use std::marker::PhantomData;

use rand::{Rand, Rng};

use super::{Proof, SxyAdvice};
use super::batch::Batch;
use super::poly::{SxEval, SyEval};
use super::parameters::{Parameters};
use super::helper::{Aggregate};

use crate::SynthesisError;

use crate::sonic::transcript::{Transcript, TranscriptProtocol};
use crate::sonic::util::*;
use crate::sonic::cs::{Backend, SynthesisDriver};
use crate::{Circuit};
use crate::sonic::sonic::AdaptorCircuit;
use crate::sonic::srs::SRS;
use crate::sonic::sonic::Nonassigning;
use super::verifier::verify_aggregate_on_srs as verify_aggregate_on_srs_sonic_circuit;
use super::verifier::verify_proofs_on_srs as verify_proofs_on_srs_sonic_circuit;

pub fn verify_proofs<E: Engine, C: Circuit<E> + Clone, R: Rng>(
    proofs: &[Proof<E>],
    inputs: &[Vec<E::Fr>],
    circuit: C,
    rng: R,
    params: &Parameters<E>,
) -> Result<bool, SynthesisError>
{
    let adapted_circuit = AdaptorCircuit(circuit);

    verify_proofs_on_srs_sonic_circuit::<_, _, Nonassigning, _>(proofs, inputs, adapted_circuit, rng, &params.srs)
}

/// Check multiple proofs with aggregation. Verifier's work is 
/// not succint due to `S(X, Y)` evaluation
pub fn verify_aggregate<E: Engine, C: Circuit<E> + Clone, R: Rng>(
    proofs: &[(Proof<E>, SxyAdvice<E>)],
    aggregate: &Aggregate<E>,
    inputs: &[Vec<E::Fr>],
    circuit: C,
    rng: R,
    params: &Parameters<E>,
) -> Result<bool, SynthesisError> {
    let adapted_circuit = AdaptorCircuit(circuit);

    verify_aggregate_on_srs_sonic_circuit::<_, _, Nonassigning, _>(proofs, aggregate, inputs, adapted_circuit, rng, &params.srs)
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
