pub mod cs;
pub mod test_assembly;
pub mod adaptor;
pub mod gates;
pub mod data_structures;
pub mod utils;
pub mod generators;
// this file is used to make prover more readable (and only for this purpose)
// cause having a very important routine, containing more than 500 lines of code is usually a bad practice
pub mod prover_stages;
pub mod prover;
//pub mod verifier;