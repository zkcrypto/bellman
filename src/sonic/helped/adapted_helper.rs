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
use super::helper::create_aggregate as create_aggregate_sonic_circuit;

pub fn create_aggregate<E: Engine, C: Circuit<E> + Clone>(
    circuit: C,
    inputs: &[(Proof<E>, SxyAdvice<E>)],
    params: &Parameters<E>,
) -> Aggregate<E>
{
    let adapted_circuit = AdaptorCircuit(circuit);

    create_aggregate_sonic_circuit::<_, _, Nonassigning>(&adapted_circuit, inputs, params)
}
