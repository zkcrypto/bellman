use crate::pairing::ff::{Field, PrimeField};
use crate::pairing::{Engine};

use crate::{SynthesisError};
use std::marker::PhantomData;
use crate::multicore::*;

use crate::redshift::polynomials::*;
use crate::redshift::IOP::oracle::*;
use crate::redshift::IOP::channel::*;
use crate::redshift::IOP::FRI::coset_combining_fri::*;
use crate::redshift::domains::*;

use super::data_structures::*;
use super::utils::*;


pub fn verify_proof<E: Engine, I: Oracle<E::Fr>, T: Channel<E::Fr, Input = I::Commitment>>(
    proof: RedshiftProof<E::Fr, I>,
    public_inputs: &[E::Fr],
    setup_precomp: &RedshiftSetupPrecomputation<E::Fr, I>,
    params: &FriParams,
    oracle_params: &I::Params,
    channel: &mut T,
) -> Result<bool, SynthesisError> 
where E::Fr : PrimeField
{

    // we assume that deg is the same for all the polynomials for now
    let n = setup_precomp.q_l_aux.deg;
    // we need n+1 to be a power of two and can not have n to be power of two
    let required_domain_size = n + 1;
    assert!(required_domain_size.is_power_of_two());

    fn find_commitment_by_label<T>(label: Label, arr: &Vec<(Label, T)>) -> Option<&T> {
        arr.iter().find(|(l, _)| *l == label).map(|(_, c)| c)
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
    let field_zero = E::Fr::zero();
    while z.pow([n as u64]) == E::Fr::one() || z == field_zero {
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

    let aggregation_challenge = channel.produce_field_element_challenge();

    let domain_size = n * params.lde_factor;
    let domain = Domain::<E::Fr>::new_for_size((domain_size) as u64)?;
    let omega = domain.generator;

    let upper_layer_combiner = |arr: Vec<(Label, &E::Fr)>| -> Option<E::Fr> {
        fn find_poly_value_at_omega<T>(label: Label, arr: &Vec<(Label, T)>) -> Option<&T> {
            arr.iter().find(|(l, _)| *l == label).map(|(_, c)| c)
        }

        // given an evaluation point x and auxiliarly point x_1,
        // aggregation_challenge = alpha (the final value of alpha is also returned!)
        // and an array of pairs (f_i(x), f_i(x_1)) - one pair for each polynomial f_i(t) in question (i \in [0, 1, .., n])
        // this function computes: 
        // y = /sum alpha^i [f_i(x) - f_i(x_1)]/ [x - x_1]
        // and returns the pair (y, final_alpha)

        fn combine_at_single_point<F: PrimeField>(pairs: Vec<(&F, F)>, x: &F, x_1: &F, alpha: &F) -> (F, F) {

            let mut res = F::zero();
            let mut aggr_mult = F::one();

            for (&a, b) in pairs.iter() {
                // separately compute numerators
                let mut temp = a;
                temp.sub_assign(&b);
                temp.mul_assign(&aggr_mult);

                res.add_assign(&temp);
                aggr_mult.mul_assign(alpha);
            }

            // now compute the common denominator
            let mut temp = *x;
            temp.sub_assign(x_1);
            temp = temp.inverse().expect("must exist");
            res.mul_assign(&temp);

            (res, aggr_mult)
        }

        // given an evaluation point x and two auxiliarly points x_1, x_2,
        // aggregation_challenge = alpha (the final value of alpha is also returned!)
        // and an array of triples (f_i(x), f_i(x_1), f_i(x_2)) - one triple for each polynomial f_i(t) in question (i \in [0, 1, .., n])
        // this function computes: 
        // y = /sum alpha^i [f_i(x) - U_i(x)]/ [(x - x_1)(x - x_2)]
        // where U_i(t) is the unique linear function, having value f_i(x_1) at x_1 and f_i(x_2) at x_2
        // note that such U_i(t) = f_i(x_1) + [t - x_1]/ [x_2 - x_1] (f_i(x_2) - f_i(x_1))  and hence
        // U_i(x) = f_i(x_1) + [x - x_1]/ [x_2 - x_1] (f_i(x_2) - f_i(x_1))
        // this means that all U_i(x) share the common slope [x - x_1] / [x_2 - x_1]
        // which therefore may be precomputed once and forall
        // funtion returns the pair (y, final_alpha)

        fn combine_at_two_points<F: PrimeField>(triples: Vec<(&F, F, F)>, x: &F, x_1: &F, x_2: &F, alpha: &F) -> (F, F) {
            
            // precompute the common slope
            let mut slope = *x;
            slope.sub_assign(x_1);
            let mut slope_denum = *x_2;
            slope_denum.sub_assign(x_1);
            slope.mul_assign(&slope_denum.inverse().expect("must exist"));

            let mut res = F::zero();
            let mut aggr_mult = F::one();

            for (&f_x, f_x_1, f_x_2) in triples.iter() {

                //evaluate interpolation poly -U_i(x) = -f_x_1 - slope * (f_x_2 - f_x_1) = slope * (f_x_1 - f_x_2) - f_x_1
                let mut temp = f_x_1.clone();
                temp.sub_assign(&f_x_2);
                temp.mul_assign(&slope);
                temp.sub_assign(&f_x_1);

                // compute nominator: aggr_mult * (f_x - U_i(x))
                temp.add_assign(&f_x);
                temp.mul_assign(&aggr_mult);

                res.add_assign(&temp);
                aggr_mult.mul_assign(alpha);
            }

            // now compute the common denominator
            // (x - x_1)(x - x_2) = x^2 - (x_1 + x_2) * x + x_1 * x_2
            let mut t_0 = *x_1;
            t_0.add_assign(x_2);
            let mut t_1 = *x_1;
            t_1.mul_assign(&x_2);

            let mut common_denominator = *x;
            common_denominator.double();
            common_denominator.sub_assign(&t_0);
            common_denominator.add_assign(&t_1);
            
            res.mul_assign(&common_denominator.inverse().expect("must exist"));
            (res, aggr_mult)

        }

        let evaluation_point = find_poly_value_at_omega("evaluation_point", &arr)?;

        // combine polynomials a, b, t_low, t_mid, t_high,
        // which are opened only at z
        let pairs : Vec<(&E::Fr, E::Fr)> = vec![
            (find_poly_value_at_omega("a", &arr)?, a_at_z),
            (find_poly_value_at_omega("b", &arr)?, b_at_z),
            (find_poly_value_at_omega("t_low", &arr)?, t_low_at_z),
            (find_poly_value_at_omega("t_mid", &arr)?, t_mid_at_z),
            (find_poly_value_at_omega("t_high", &arr)?, t_high_at_z),
        ];

        let (mut res1, mut alpha1) = combine_at_single_point(pairs, &evaluation_point, &z, &aggregation_challenge);

        // combine witness polynomials z_1, z_2, c which are opened at z and z * omega

        let mut z_shifted = z;
        z_shifted.mul_assign(&omega);

        let witness_triples : Vec<(&E::Fr, E::Fr, E::Fr)> = vec![
            (find_poly_value_at_omega("z_1", &arr)?, z_1_at_z, z_1_shifted_at_z),
            (find_poly_value_at_omega("z_2", &arr)?, z_2_at_z, z_2_shifted_at_z),
            (find_poly_value_at_omega("c", &arr)?, c_at_z, c_shifted_at_z),
        ];

        let (mut res2, alpha2) = combine_at_two_points(witness_triples, &evaluation_point, &z, &z_shifted, &aggregation_challenge);

        // finally combine setup polynomials q_l, q_r, q_o, q_m, q_c, q_add_sel, s_id, sigma_1, sigma_2, sigma_3
        // which are opened at z and z_setup
        // in current implementation we assume that setup point is the same for all circuit-defining polynomials!

        let setup_aux = vec![
            &setup_precomp.q_l_aux, &setup_precomp.q_r_aux, &setup_precomp.q_o_aux, &setup_precomp.q_m_aux, 
            &setup_precomp.q_c_aux, &setup_precomp.q_add_sel_aux, &setup_precomp.s_id_aux, &setup_precomp.sigma_1_aux, 
            &setup_precomp.sigma_2_aux, &setup_precomp.sigma_3_aux,
        ];
        assert!(setup_aux.windows(2).all(|w| w[0].setup_point == w[1].setup_point));
        let common_setup_point = setup_precomp.q_l_aux.setup_point;

        let setup_triples : Vec<(&E::Fr, E::Fr, E::Fr)> = vec![
            (find_poly_value_at_omega("q_l", &arr)?, q_l_at_z, setup_precomp.q_l_aux.setup_value),
            (find_poly_value_at_omega("q_r", &arr)?, q_r_at_z, setup_precomp.q_r_aux.setup_value),
            (find_poly_value_at_omega("q_o", &arr)?, q_o_at_z, setup_precomp.q_o_aux.setup_value),
            (find_poly_value_at_omega("q_m", &arr)?, q_m_at_z, setup_precomp.q_m_aux.setup_value),
            (find_poly_value_at_omega("q_c", &arr)?, q_c_at_z, setup_precomp.q_c_aux.setup_value),
            (find_poly_value_at_omega("q_add_sel", &arr)?, q_add_sel_at_z, setup_precomp.q_add_sel_aux.setup_value),
            (find_poly_value_at_omega("s_id", &arr)?, s_id_at_z, setup_precomp.s_id_aux.setup_value),
            (find_poly_value_at_omega("sigma_1", &arr)?, sigma_1_at_z, setup_precomp.sigma_1_aux.setup_value),
            (find_poly_value_at_omega("sigma_2", &arr)?, sigma_2_at_z, setup_precomp.sigma_2_aux.setup_value),
            (find_poly_value_at_omega("sigma_3", &arr)?, sigma_3_at_z, setup_precomp.sigma_3_aux.setup_value),
        ];

        let (mut res3, _) = combine_at_two_points(setup_triples, &evaluation_point, &z, &common_setup_point, &aggregation_challenge);

        // res = res1 + res2 * alpha_1 + res_3 * alpha_1 * alpha_2
        res2.mul_assign(&alpha1);
        res1.add_assign(&res2);
        alpha1.mul_assign(&alpha2);
        res3.mul_assign(&alpha1);
        res1.add_assign(&res3);

        Some(res1)
    };

    let setup_poly_commitmetns = vec![
        ("q_l", setup_precomp.q_l_aux.oracle.get_commitment()),
        ("q_r", setup_precomp.q_r_aux.oracle.get_commitment()),
        ("q_o", setup_precomp.q_o_aux.oracle.get_commitment()),
        ("q_m", setup_precomp.q_m_aux.oracle.get_commitment()),
        ("q_c", setup_precomp.q_c_aux.oracle.get_commitment()),
        ("q_add_sel", setup_precomp.q_add_sel_aux.oracle.get_commitment()),
        ("s_id", setup_precomp.s_id_aux.oracle.get_commitment()),
        ("sigma_1", setup_precomp.sigma_1_aux.oracle.get_commitment()),
        ("sigma_2", setup_precomp.sigma_2_aux.oracle.get_commitment()),
        ("sigma_3", setup_precomp.sigma_3_aux.oracle.get_commitment()),
    ];

    let mut upper_layer_commitments = proof.commitments.clone();
    upper_layer_commitments.extend(setup_poly_commitmetns.into_iter());
      
    let fri_challenges = FriIop::get_fri_challenges(
        &proof.batched_FRI_proof,
        channel,
        &params,
    ); 
    let natural_first_element_indexes = (0..params.R).map(|_| channel.produce_uint_challenge() as usize % domain_size).collect();

    let is_valid = FriIop::<E::Fr, I, T>::verify_proof_queries(
        &proof.batched_FRI_proof,
        upper_layer_commitments,
        natural_first_element_indexes,
        &fri_challenges[..],
        &params,
        oracle_params,
        upper_layer_combiner)?;

    Ok(is_valid)
}


