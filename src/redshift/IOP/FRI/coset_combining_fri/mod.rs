pub mod fri;
pub mod query_producer;
pub mod verifier;
pub mod precomputation;

use crate::SynthesisError;
use crate::multicore::Worker;
use crate::ff::PrimeField;

use crate::redshift::IOP::oracle::Oracle;
use crate::redshift::polynomials::*;
use crate::redshift::IOP::channel::Channel;

//proof prototype is just a series of FRI-oracles (FRI setup phase)
pub trait FriProofPrototype<F: PrimeField, I: Oracle<F>> {
    fn get_commitments(&self) -> Vec<I::Commitment>;
    fn get_final_root(&self) -> I::Commitment;
    //coefficients of the polynomials on the bottom letter of FRI
    fn get_final_coefficients(&self) -> Vec<F>;
}

//result of FRI query phase (r iterations)
//the parameter r is defined in FRI params  
pub trait FriProof<F: PrimeField, I: Oracle<F>> {
    fn get_final_coefficients(&self) -> &[F];
    fn get_queries(&self) -> &Vec<Vec<I::Query>>;
}

pub trait FriPrecomputations<F: PrimeField> {
    fn new_for_domain_size(size: usize) -> Self;
    fn omegas_inv_bitreversed(&self) -> &[F];
    fn domain_size(&self) -> usize;
}

pub trait FriParams<F: PrimeField> : Clone + std::fmt::Debug {
    //power of 2 - it measures how much nearby levels of FRI differ in size (nu in the paper)
    const COLLAPSING_FACTOR : usize;
    //number of iterations done during FRI query phase
    const R : usize;
    //the degree of the resulting polynomial at the bottom level of FRI
    const OUTPUT_POLY_DEGREE : usize,

    pub type OracleType: Oracle<F>;
    pub type Channel: Channel<F, Input = Self::OracleType::Commitment>;
    pub type ProofPrototype: FriProofPrototype<F, Self::OracleType>;
    pub type Proof: FriProof<F, Self::OracleType>;
}

pub trait FriIOP<F: PrimeField> {
    type Params = FriParams<F>;

    fn proof_from_lde<P: Self::Params::Channel, C: FriPrecomputations<F>>
    (
        //valuse of the polynomial on FRI domain
        lde_values: &Polynomial<F, Values>,
        lde_factor: usize,
        precomputations: &C,
        worker: &Worker,
        channel: &mut P,
        params: &Self::Params
    ) -> Result<Self::FriParams::ProofPrototype, SynthesisError>;

    fn prototype_into_proof(
        prototype: Self::ProofPrototype,
        iop_values: &Polynomial<F, Values>,
        natural_first_element_indexes: Vec<usize>,
        params: &Self::Params
    ) -> Result<Self::Proof, SynthesisError>;

    fn get_fri_challenges<P: Prng<F, Input = <Self::IopType as IopInstance<F>>::Commitment>>(
        proof: &Self::Proof,
        prng: &mut P,
        params: &Self::Params
    ) -> Vec<F>;

    fn verify_proof_with_challenges(
        proof: &Self::Proof,
        natural_element_indexes: Vec<usize>,
        expected_value: &[F],
        fri_challenges: &[F],
        params: &Self::Params
    ) -> Result<bool, SynthesisError>;
}