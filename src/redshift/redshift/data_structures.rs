use crate::pairing::ff::{Field, PrimeField};
use crate::pairing::{Engine};

use crate::multicore::*;
use crate::redshift::polynomials::*;
use crate::redshift::IOP::oracle::*;
use crate::redshift::IOP::FRI::coset_combining_fri::*;


#[derive(Debug)]
pub struct RedshiftSetup<F: PrimeField, I: Oracle<F>>{
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

pub struct SinglePolySetupData<F: PrimeField, I: Oracle<F>>{
    pub poly: Polynomial<F, Values>,
    pub deg: usize,
    pub oracle: I,
    pub setup_point: F,
    pub setup_value: F,
}

pub struct SinglePolyCommitmentData<F: PrimeField, I: Oracle<F>>{
    pub poly: Polynomial<F, Values>,
    pub deg: usize,
    pub oracle: I,
}

// #[derive(Debug)]
pub struct RedshiftSetupPrecomputation<F: PrimeField, I: Oracle<F>>{
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

pub struct SinglePointOpeningRequest<'a, F: PrimeField> {
    polynomials: Vec<&'a Polynomial<F, Values>>,
    opening_point: F,
    opening_values: Vec<F>,
}

pub struct DoublePointOpeningRequest<'a, F: PrimeField> {
    polynomials: Vec<&'a Polynomial<F, Values>>,
    first_opening_point: F,
    first_point_values: Vec<F>,
    second_opening_point: F,
    second_open_values: Vec<F>,
}

pub struct RedshiftProof<F: PrimeField, I: Oracle<F>>{
    pub a_opening_value: F,
    pub b_opening_value: F,
    pub c_opening_value: F,
    pub q_l_opening_value: F,
    pub q_r_opening_value: F,
    pub q_o_opening_value: F,
    pub q_m_opening_value: F,
    pub q_c_opening_value: F,
    pub q_add_sel_opening_value: F,
    pub s_id_opening_value: F,
    pub sigma_1_opening_value: F,
    pub sigma_2_opening_value: F,
    pub sigma_3_opening_value: F,
    pub z_1_opening_value: F,
    pub z_2_opening_value: F,
    pub z_1_shifted_opening_value: F,
    pub z_2_shifted_opening_value: F,
    pub t_low_opening_value: F,
    pub t_mid_opening_value: F,
    pub t_high_opening_value: F,
    pub a_commitment: I::Commitment,
    pub b_commitment: I::Commitment,
    pub c_commitment: I::Commitment,
    pub z_1_commitment: I::Commitment,
    pub z_2_commitment: I::Commitment,
    pub t_low_commitment: I::Commitment,
    pub t_mid_commitment: I::Commitment,
    pub t_high_commitment: I::Commitment,
    pub batched_FRI_proof: FriProof<F, I>,
}


    
    

  