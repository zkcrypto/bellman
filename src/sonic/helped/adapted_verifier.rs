use pairing::ff::{Field};
use pairing::{Engine, CurveProjective};
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
use crate::sonic::cs::Nonassigning;
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


