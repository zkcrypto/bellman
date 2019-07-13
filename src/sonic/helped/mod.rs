use crate::pairing::ff::{Field};
use crate::pairing::{Engine, CurveProjective};
use std::marker::PhantomData;

pub mod batch;
pub mod poly;
pub mod prover;
pub mod verifier;
pub mod helper;
pub mod parameters;
pub mod generator;
mod adapted_prover;
mod adapted_verifier;
mod adapted_helper;

pub use self::batch::{Batch};
pub use self::verifier::{MultiVerifier};

pub use self::generator::{
    CircuitParameters, 
    generate_parameters, 
    generate_parameters_on_srs, 
    generate_parameters_on_srs_and_information, 
    generate_random_parameters, 
    generate_srs,
    get_circuit_parameters,
    get_circuit_parameters_for_succinct_sonic
};
pub use self::parameters::{
    Proof, 
    SxyAdvice, 
    Parameters, 
    VerifyingKey, 
    PreparedVerifyingKey
};
pub use self::adapted_prover::{
    create_advice,
    create_advice_on_srs,
    create_advice_on_information_and_srs, 
    create_proof, 
    create_proof_on_srs, 
};

pub use self::adapted_verifier::{
    verify_proofs,
    verify_aggregate
};

pub use self::adapted_helper::{
    create_aggregate
};