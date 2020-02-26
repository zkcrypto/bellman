use crate::pairing::ff::{Field, PrimeField};
use crate::pairing::{Engine};

use crate::plonk::commitments::transparent::fri::coset_combining_fri::fri::*;
use crate::plonk::commitments::transparent::iop_compiler::*;

#[derive(Debug, Clone)]
pub struct RedshiftParameters<F: PrimeField>{
    pub lde_factor: usize,
    pub num_queries: usize,
    pub output_coeffs_at_degree_plus_one: usize,
    pub coset_params: CosetParams<F>,
}

#[derive(Debug)]
pub struct RedshiftSetup<F: PrimeField, I: IopInstance<F>>{
    pub n: usize,
    pub q_l: I::Commitment,
    pub q_r: I::Commitment,
    pub q_o: I::Commitment,
    pub q_m: I::Commitment,
    pub q_c: I::Commitment,
    pub q_add_sel: I::Commitment,
    pub s_id: I::Commitment,
    pub sigma_1: I::Commitment,
    pub sigma_2: I::Commitment,
    pub sigma_3: I::Commitment,
}