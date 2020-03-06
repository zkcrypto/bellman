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
    const OUTPUT_POLY_DEGREE : usize;

    type OracleType: Oracle<F>;
    type Channel: Channel<F, Input = Self::OracleType::Commitment>;
    type ProofPrototype: FriProofPrototype<F, Self::OracleType>;
    type Proof: FriProof<F, Self::OracleType>;
}

pub trait FriIop<F: PrimeField> {
    type Params : FriParams<F>;

    fn proof_from_lde<C: FriPrecomputations<F>>
    (
        //valuse of the polynomial on FRI domain
        lde_values: &Polynomial<F, Values>,
        lde_factor: usize,
        precomputations: &C,
        worker: &Worker,
        channel: &mut <Self::Params as FriParams<F>>::Channel,
        params: &Self::Params
    ) -> Result<<Self::Params as FriParams<F>>::ProofPrototype, SynthesisError>;

    // fn prototype_into_proof(
    //     prototype: Self::Params::ProofPrototype,
    //     iop_values: &Polynomial<F, Values>,
    //     natural_first_element_indexes: Vec<usize>,
    //     params: &Self::Params
    // ) -> Result<Self::Proof, SynthesisError>;

    // fn get_fri_challenges<P: Prng<F, Input = <Self::IopType as IopInstance<F>>::Commitment>>(
    //     proof: &Self::Proof,
    //     prng: &mut P,
    //     params: &Self::Params
    // ) -> Vec<F>;

    // fn verify_proof_with_challenges(
    //     proof: &Self::Proof,
    //     natural_element_indexes: Vec<usize>,
    //     expected_value: &[F],
    //     fri_challenges: &[F],
    //     params: &Self::Params
    // ) -> Result<bool, SynthesisError>;
}

pub fn log2_floor(num: usize) -> u32 {
    assert!(num > 0);

    let mut pow = 0;

    while (1 << (pow+1)) <= num {
        pow += 1;
    }

    pow
}