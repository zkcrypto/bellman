use crate::pairing::ff::{Field, PrimeField};
use crate::pairing::{Engine};

use crate::multicore::*;
use crate::redshift::polynomials::*;
use crate::redshift::IOP::oracle::*;


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

pub struct OpeningRequest<'a, F: PrimeField> {
    pub polynomial: &'a Polynomial<F, Values>,
    pub deg: usize,
    pub opening_points: (F, Option<F>),
    pub opening_values: (F, Option<F>),
}


    
    

  