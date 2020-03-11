pub mod fri;
pub mod coset_combiner;
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
#[derive(PartialEq, Eq, Clone)]
pub struct FriProofPrototype<F: PrimeField, I: Oracle<F>> {
    //including the initial one
    pub oracles: Vec<I>,
    pub challenges: Vec<F>,
    //this vector include the initial and doesn't include the last one
    pub intermediate_values: Vec<Polynomial<F, Values>>,
    //coefficients of the polynomials on the bottom letter of FRI
    pub final_coefficients: Vec<F>,
    pub initial_degree_plus_one : usize,
    pub lde_factor: usize,
    pub collapsing_factor: usize,
}

impl<F: PrimeField, I: Oracle<F>> FriProofPrototype<F, I> {
    fn get_roots(&self) -> Vec<I::Commitment> {
        let mut roots = vec![];
        for c in self.oracles.iter() {
            roots.push(c.get_commitment().clone());
        }
        roots
    }

    fn get_final_coefficients(&self) -> Vec<F> {
        self.final_coefficients.clone()
    }
}

//result of FRI query phase (r iterations)
//the parameter r is defined in FRI params 
#[derive(PartialEq, Eq, Clone)]
pub struct FriProof<F: PrimeField, I: Oracle<F>> {
    pub queries: Vec<Vec<I::Query>>,
    pub commitments: Vec<I::Commitment>,
    pub final_coefficients: Vec<F>,
    pub initial_degree_plus_one : usize,
    pub lde_factor: usize,
    pub collapsing_factor: usize,
}

impl<F: PrimeField, I: Oracle<F>> FriProof<F, I> {
    fn get_final_coefficients(&self) -> &[F] {
        &self.final_coefficients
    }

    fn get_queries(&self) -> &Vec<Vec<I::Query>> {
        &self.queries
    }
}

pub trait FriPrecomputations<F: PrimeField> {
    fn new_for_domain_size(size: usize) -> Self;
    fn omegas_inv_bitreversed(&self) -> &[F];
    fn domain_size(&self) -> usize;
}

#[derive(Debug, Clone)]
pub struct FriParams {
    //it measures how much nearby levels of FRI differ in size (nu in the paper)
    // it is 1 for 2 -> 1 mapping, 2 for 4 -> 1 mapping, etc.
    pub collapsing_factor : usize,
    //number of iterations done during FRI query phase
    pub R : usize,
    //the degree of the resulting polynomial at the bottom level of FRI
    pub output_poly_degree : usize,
}

//TODO: paranetrize FriIop with coset combiner also
pub struct FriIop<F: PrimeField, O: Oracle<F>, C: Channel<F, Input = O::Commitment>> {
    _marker_f: std::marker::PhantomData<F>,
    _marker_oracle: std::marker::PhantomData<O>,
    _marker_channel: std::marker::PhantomData<C>,
}