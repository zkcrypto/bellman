use crate::pairing::ff::{Field, PrimeField};
use crate::pairing::{Engine};

use crate::{SynthesisError};
use std::marker::PhantomData;
use crate::multicore::*;

use crate::redshift::polynomials::*;
use crate::redshift::IOP::oracle::*;
use crate::redshift::IOP::channel::*;
use crate::redshift::IOP::FRI::coset_combining_fri::*;

use super::data_structures::*;
use super::utils::*;


pub fn verify_proof<E: Engine, I: Oracle<E::Fr>, T: Channel<E::Fr, Input = I::Commitment>>(
    proof: RedshiftProof<E::Fr, I>,
    public_inputs: &[E::Fr],
    setup_precomp: &RedshiftSetupPrecomputation<E::Fr, I>,
    params: &FriParams,
) -> Result<bool, SynthesisError> {
    
    let mut channel = T::new();

    // we assume that deg is the same for all the polynomials for now
    let n = setup_precomp.q_l_aux.deg;
    // we need n+1 to be a power of two and can not have n to be power of two
    let required_domain_size = n + 1;
    assert!(required_domain_size.is_power_of_two());

    fn find_commitment_by_label<T>(label: Label, arr: &Vec<(Label, T)>) -> Option<&T> {
        arr.iter().find(|(l, c)| *l == label).map(|(l, c)| c)
    }

    match find_commitment_by_label("a", &proof.commitments) {
        None => return Ok(false),
        Some(x) => channel.consume(x),
    };

    match find_commitment_by_label("b", &proof.commitments) {
        None => return Ok(false),
        Some(x) => channel.consume(x),
    };

    match find_commitment_by_label("c", &proof.commitments) {
        None => return Ok(false),
        Some(x) => channel.consume(x),
    };

    let beta = channel.produce_field_element_challenge();
    let gamma = channel.produce_field_element_challenge();

    match find_commitment_by_label("z_1", &proof.commitments) {
        None => return Ok(false),
        Some(x) => channel.consume(x),
    };

    match find_commitment_by_label("z_2", &proof.commitments) {
        None => return Ok(false),
        Some(x) => channel.consume(x),
    };

    let alpha = channel.produce_field_element_challenge();

    match find_commitment_by_label("t_low", &proof.commitments) {
        None => return Ok(false),
        Some(x) => channel.consume(x),
    };

    match find_commitment_by_label("t_mid", &proof.commitments) {
        None => return Ok(false),
        Some(x) => channel.consume(x),
    };

    match find_commitment_by_label("t_high", &proof.commitments) {
        None => return Ok(false),
        Some(x) => channel.consume(x),
    };

    let mut z = E::Fr::one();
    while z.pow([n as u64]) == E::Fr::one() {
        z = channel.produce_field_element_challenge();
    }

    // this is a sanity check of the final equation

    let a_at_z = proof.a_opening_value;
    let b_at_z = proof.b_opening_value;
    let c_at_z = proof.c_opening_value;
    let c_shifted_at_z = proof.c_shifted_opening_value;

    let q_l_at_z = proof.q_l_opening_value;
    let q_r_at_z = proof.q_r_opening_value;
    let q_o_at_z = proof.q_o_opening_value;
    let q_m_at_z = proof.q_m_opening_value;
    let q_c_at_z = proof.q_c_opening_value;
    let q_add_sel_at_z = proof.q_add_sel_opening_value;

    let s_id_at_z = proof.s_id_opening_value;
    let sigma_1_at_z = proof.sigma_1_opening_value;
    let sigma_2_at_z = proof.sigma_2_opening_value;
    let sigma_3_at_z = proof.sigma_3_opening_value;

    let mut inverse_vanishing_at_z = evaluate_inverse_vanishing_poly::<E>(required_domain_size, z);

    let z_1_at_z = proof.z_1_opening_value;
    let z_2_at_z = proof.z_2_opening_value;

    let z_1_shifted_at_z = proof.z_1_shifted_opening_value;
    let z_2_shifted_at_z = proof.z_2_shifted_opening_value;

    let l_0_at_z = evaluate_lagrange_poly::<E>(required_domain_size, 0, z);
    let l_n_minus_one_at_z = evaluate_lagrange_poly::<E>(required_domain_size, n - 1, z);

    let mut PI_at_z = E::Fr::zero();
    for (i, val) in public_inputs.iter().enumerate() {
        if i == 0 {
            let mut temp = l_0_at_z;
            temp.mul_assign(val);
            PI_at_z.sub_assign(&temp);
        }
        else {
            // TODO: maybe make it multithreaded
            let mut temp = evaluate_lagrange_poly::<E>(required_domain_size, i, z);
            temp.mul_assign(val);
            PI_at_z.sub_assign(&temp);
        }
    }

    let t_low_at_z = proof.t_low_opening_value;
    let t_mid_at_z = proof.t_mid_opening_value;
    let t_high_at_z = proof.t_high_opening_value;

    let z_in_pow_of_domain_size = z.pow([required_domain_size as u64]);

    let mut t_at_z = E::Fr::zero();
    t_at_z.add_assign(&t_low_at_z);

    let mut tmp = z_in_pow_of_domain_size;
    tmp.mul_assign(&t_mid_at_z);
    t_at_z.add_assign(&tmp);

    let mut tmp = z_in_pow_of_domain_size;
    tmp.mul_assign(&z_in_pow_of_domain_size);
    tmp.mul_assign(&t_high_at_z);
    t_at_z.add_assign(&tmp);

    let mut t_1 = {
        let mut res = q_c_at_z;

        let mut tmp = q_l_at_z;
        tmp.mul_assign(&a_at_z);
        res.add_assign(&tmp);

        let mut tmp = q_r_at_z;
        tmp.mul_assign(&b_at_z);
        res.add_assign(&tmp);

        let mut tmp = q_o_at_z;
        tmp.mul_assign(&c_at_z);
        res.add_assign(&tmp);

        let mut tmp = q_m_at_z;
        tmp.mul_assign(&a_at_z);
        tmp.mul_assign(&b_at_z);
        res.add_assign(&tmp);

        // add additional shifted selector
        let mut tmp = q_add_sel_at_z;
        tmp.mul_assign(&c_shifted_at_z);
        res.add_assign(&tmp);

        // add public inputs
        res.add_assign(&PI_at_z);

        // no need for the first one
        //inverse_vanishing_at_z.mul_assign(&alpha);

        res.mul_assign(&inverse_vanishing_at_z);

        res
    };

    let n_fe = E::Fr::from_str(&n.to_string()).expect("must be valid field element");
    let mut two_n_fe = n_fe;
    two_n_fe.double();

    {
        let mut res = z_1_at_z;

        let mut tmp = s_id_at_z;
        tmp.mul_assign(&beta);
        tmp.add_assign(&a_at_z);
        tmp.add_assign(&gamma);
        res.mul_assign(&tmp);

        let mut tmp = s_id_at_z;
        tmp.add_assign(&n_fe);
        tmp.mul_assign(&beta);
        tmp.add_assign(&b_at_z);
        tmp.add_assign(&gamma);
        res.mul_assign(&tmp);

        let mut tmp = s_id_at_z;
        tmp.add_assign(&two_n_fe);
        tmp.mul_assign(&beta);
        tmp.add_assign(&c_at_z);
        tmp.add_assign(&gamma);
        res.mul_assign(&tmp);

        res.sub_assign(&z_1_shifted_at_z);

        inverse_vanishing_at_z.mul_assign(&alpha);

        res.mul_assign(&inverse_vanishing_at_z);

        t_1.add_assign(&res);
    }

    {
        let mut res = z_2_at_z;

        let mut tmp = sigma_1_at_z;
        tmp.mul_assign(&beta);
        tmp.add_assign(&a_at_z);
        tmp.add_assign(&gamma);
        res.mul_assign(&tmp);

        let mut tmp = sigma_2_at_z;
        tmp.mul_assign(&beta);
        tmp.add_assign(&b_at_z);
        tmp.add_assign(&gamma);
        res.mul_assign(&tmp);

        let mut tmp = sigma_3_at_z;
        tmp.mul_assign(&beta);
        tmp.add_assign(&c_at_z);
        tmp.add_assign(&gamma);
        res.mul_assign(&tmp);

        res.sub_assign(&z_2_shifted_at_z);

        inverse_vanishing_at_z.mul_assign(&alpha);

        res.mul_assign(&inverse_vanishing_at_z);

        t_1.add_assign(&res);
    }

    {
        let mut res = z_1_shifted_at_z;
        res.sub_assign(&z_2_shifted_at_z);
        res.mul_assign(&l_n_minus_one_at_z);

        inverse_vanishing_at_z.mul_assign(&alpha);

        res.mul_assign(&inverse_vanishing_at_z);

        t_1.add_assign(&res);
    }

    {
        let mut res = z_1_at_z;
        res.sub_assign(&z_2_at_z);
        res.mul_assign(&l_0_at_z);

        inverse_vanishing_at_z.mul_assign(&alpha);

        res.mul_assign(&inverse_vanishing_at_z);

        t_1.add_assign(&res);
    }

    if t_1 != t_at_z {
        println!("Recalculated t(z) is not equal to the provided value");
        return Ok(false);
    }

    // verify FRI proof;
    
    let fri_challenges = FriIop::get_fri_challenges(
        &proof.batched_FRI_proof,
        &mut channel,
        &params,
    ); 

    let domain_size = n * params.lde_factor;
    let natural_first_element_indexes = (0..params.R).map(|_| channel.produce_uint_challenge() as usize % domain_size).collect();

    fn upper_layer_combiner<F: PrimeField>(arr: Vec<(Label, &F)>) -> F {
        // combine witness polynomials a, b, t_low, t_mid, t_high which are opened only at z
        
        let pairs = vec![
            
        ]

        // combine witness polynomials c, z_1, z_2 which are opened at z and z * omega,

        // combine setup polynomials q_l, q_r, q_o, q_m, q_c, q_add_sel, s_id, sigma_1, sigma_2, sigma_3
        // which are opened at z_setup and z 

    }

    pub a_opening_value: F,
    pub b_opening_value: F,
    pub c_opening_value: F,
    pub c_shifted_opening_value: F,
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

    FriIop::
    verify_proof_queries<Func: Fn(Vec<&F>) -> F>(
        proof: &FriProof<F, O>,
        upper_layer_commitments: Vec<(Label, O::Commitment)>,
        natural_element_indexes: Vec<usize>,
        fri_challenges: &[F],
        params: &FriParams,
        upper_layer_combiner: Func

    
    

    let valid = committer.verify_multiple_openings(commitments, opening_points, &claimed_values, aggregation_challenge, &proof.openings_proof, &mut transcript);


    Ok(valid)
}


