use crate::pairing::ff::{Field, PrimeField};
use crate::pairing::{Engine};

use crate::plonk::commitments::transparent::fri::coset_combining_fri::fri::*;
use crate::plonk::commitments::transparent::iop_compiler::*;
use crate::plonk::polynomials::*;
use crate::plonk::fft::cooley_tukey_ntt::*;
use crate::multicore::*;

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

pub struct SinglePolySetupData<F: PrimeField, I: IopInstance<F>>{
    pub poly: Polynomial<F, Values>,
    pub oracle: I,
    pub setup_point: F,
    pub setup_value: F,
}

pub struct SinglePolyCommitmentData<F: PrimeField, I: IopInstance<F>>{
    pub poly: Polynomial<F, Values>,
    pub oracle: I,
}

// #[derive(Debug)]
pub struct RedshiftSetupPrecomputation<F: PrimeField, I: IopInstance<F>>{
    pub q_l_aux: SinglePolySetupData<F, I>,
    pub q_r_aux: SinglePolySetupData<F, I>,
    pub q_o_aux: SinglePolySetupData<F, I>,
    pub q_m_aux: SinglePolySetupData<F, I>,
    pub q_c_aux: SinglePolySetupData<F, I>,
    pub q_add_sel_aux: SinglePolySetupData<F, I>,
    pub s_id_aux: SinglePolySetupData<F, I>,
    pub sigma_1_aux: SinglePolySetupData<F, I>,
    pub sigma_2_aux: SinglePolySetupData<F, I>,
    pub sigma_3_aux: SinglePolySetupData<F, I>,
}

pub struct WitnessOpeningRequest<'a, F: PrimeField> {
    pub polynomials: Vec<&'a Polynomial<F, Values>>,
    pub opening_point: F,
    pub opening_values: Vec<F>
}

pub struct SetupOpeningRequest<'a, F: PrimeField> {
    pub polynomials: Vec<&'a Polynomial<F, Values>>,
    pub setup_point: F,
    pub setup_values: Vec<F>,
    pub opening_point: F,
    pub opening_values: Vec<F>
}


    
    

  