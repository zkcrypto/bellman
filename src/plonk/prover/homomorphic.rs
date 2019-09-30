use crate::pairing::ff::{Field, PrimeField};
use crate::pairing::{Engine};

use crate::{SynthesisError};
use std::marker::PhantomData;

use crate::plonk::cs::gates::*;
use crate::plonk::cs::*;

use crate::multicore::*;
use super::polynomials::*;
use super::domains::*;
use crate::plonk::commitments::*;
use crate::plonk::commitments::transcript::*;
use crate::plonk::utils::*;

pub struct PlonkNonhomomorphicProof<E: Engine, S: CommitmentScheme<E::Fr> >{
    q_l_opening_value: E::Fr,
    q_r_opening_value: E::Fr,
    q_o_opening_value: E::Fr,
    q_m_opening_value: E::Fr,
    q_c_opening_value: E::Fr,
    s_id_opening_value: E::Fr,
    sigma_1_opening_value: E::Fr,
    sigma_2_opening_value: E::Fr,
    sigma_3_opening_value: E::Fr,
    z_1_shifted_opening_value: E::Fr,
    z_2_shifted_opening_value: E::Fr,
    r_opening_value: E::Fr,
    unshifted_openings_proof: S::OpeningProof,
    shifted_openings_proof: S::OpeningProof,

}

pub fn prove_nonhomomorphic<E: Engine, S: CommitmentScheme<E::Fr>, T: Transcript<E::Fr, Input = S::Commitment>, C: Circuit<E>>(circuit: &C, committer: &S) -> Result<PlonkNonhomomorphicProof<E, S>, SynthesisError> {
    let mut assembly = ProvingAssembly::<E>::new();
    circuit.synthesize(&mut assembly)?;
    assembly.finalize();

    let worker = Worker::new();

    let mut transcript = T::new();

    let n = assembly.input_gates.len() + assembly.aux_gates.len();

    // we need n+1 to be a power of two and can not have n to be power of two
    let required_domain_size = n + 1;
    assert!(required_domain_size.is_power_of_two());

    let (w_l, w_r, w_o) = assembly.make_wire_assingments();

    let w_l = Polynomial::<E::Fr, Values>::from_values_unpadded(w_l)?;
    let w_r = Polynomial::<E::Fr, Values>::from_values_unpadded(w_r)?;
    let w_o = Polynomial::<E::Fr, Values>::from_values_unpadded(w_o)?;

    let a_poly = w_l.clone_padded_to_domain()?.ifft(&worker);
    let b_poly = w_r.clone_padded_to_domain()?.ifft(&worker);
    let c_poly = w_o.clone_padded_to_domain()?.ifft(&worker);

    let (a_commitment, a_aux_data) = committer.commit_single(&a_poly);
    let (b_commitment, b_aux_data) = committer.commit_single(&b_poly);
    let (c_commitment, c_aux_data) = committer.commit_single(&c_poly);

    transcript.commit_input(&a_commitment);
    transcript.commit_input(&b_commitment);
    transcript.commit_input(&c_commitment);

    // TODO: Add public inputs

    println!("Committed A, B and C polys");

    let beta = transcript.get_challenge();
    let gamma = transcript.get_challenge();

    let mut w_l_plus_gamma = w_l.clone();
    w_l_plus_gamma.add_constant(&worker, &gamma);

    let mut w_r_plus_gamma = w_r.clone();
    w_r_plus_gamma.add_constant(&worker, &gamma);

    let mut w_o_plus_gamma = w_o.clone();
    w_o_plus_gamma.add_constant(&worker, &gamma);

    let z_1 = {
        let n = assembly.input_gates.len() + assembly.aux_gates.len();
        let s_id_1: Vec<_> = (1..=n).collect();
        let s_id_1 = convert_to_field_elements(&s_id_1, &worker);
        let s_id_1 = Polynomial::<E::Fr, Values>::from_values_unpadded(s_id_1)?;
        let mut w_l_contribution = w_l_plus_gamma.clone();
        w_l_contribution.add_assign_scaled(&worker, &s_id_1, &beta);
        drop(s_id_1);

        let s_id_2: Vec<_> = ((n+1)..=(2*n)).collect();
        let s_id_2 = convert_to_field_elements(&s_id_2, &worker);
        let s_id_2 = Polynomial::<E::Fr, Values>::from_values_unpadded(s_id_2)?;
        let mut w_r_contribution = w_r_plus_gamma.clone();
        w_r_contribution.add_assign_scaled(&worker, &s_id_2, &beta);
        drop(s_id_2);
        w_l_contribution.mul_assign(&worker, &w_r_contribution);
        drop(w_r_contribution);

        let s_id_3: Vec<_> = ((2*n+1)..=(3*n)).collect();
        let s_id_3 = convert_to_field_elements(&s_id_3, &worker);
        let s_id_3 = Polynomial::<E::Fr, Values>::from_values_unpadded(s_id_3)?;
        let mut w_o_contribution = w_o_plus_gamma.clone();
        w_o_contribution.add_assign_scaled(&worker, &s_id_3, &beta);
        drop(s_id_3);
        w_l_contribution.mul_assign(&worker, &w_o_contribution);
        drop(w_o_contribution);

        let grand_product = w_l_contribution.calculate_grand_product(&worker)?;

        // let grand_product_serial = w_l_contribution.calculate_grand_product_serial()?;

        // assert!(grand_product == grand_product_serial);

        drop(w_l_contribution);

        let values = grand_product.into_coeffs();
        assert!((values.len() + 1).is_power_of_two());
        let mut prepadded = Vec::with_capacity(values.len() + 1);
        prepadded.push(E::Fr::one());
        prepadded.extend(values);

        Polynomial::<E::Fr, Values>::from_values(prepadded)?
    };

    let z_2 = {
        let (sigma_1, sigma_2, sigma_3) = assembly.calculate_permutations_as_in_a_paper();

        let sigma_1 = convert_to_field_elements(&sigma_1, &worker);
        let sigma_1 = Polynomial::<E::Fr, Values>::from_values_unpadded(sigma_1)?;
        let mut w_l_contribution = w_l_plus_gamma.clone();
        w_l_contribution.add_assign_scaled(&worker, &sigma_1, &beta);
        drop(sigma_1);

        let sigma_2 = convert_to_field_elements(&sigma_2, &worker);
        let sigma_2 = Polynomial::<E::Fr, Values>::from_values_unpadded(sigma_2)?;
        let mut w_r_contribution = w_r_plus_gamma.clone();
        w_r_contribution.add_assign_scaled(&worker, &sigma_2, &beta);
        drop(sigma_2);
        w_l_contribution.mul_assign(&worker, &w_r_contribution);
        drop(w_r_contribution);

        let sigma_3 = convert_to_field_elements(&sigma_3, &worker);
        let sigma_3 = Polynomial::<E::Fr, Values>::from_values_unpadded(sigma_3)?;
        let mut w_o_contribution = w_o_plus_gamma.clone();
        w_o_contribution.add_assign_scaled(&worker, &sigma_3, &beta);
        drop(sigma_3);
        w_l_contribution.mul_assign(&worker, &w_o_contribution);
        drop(w_o_contribution);

        let grand_product = w_l_contribution.calculate_grand_product(&worker)?;

        // let grand_product_serial = w_l_contribution.calculate_grand_product_serial()?;

        // assert!(grand_product == grand_product_serial);

        drop(w_l_contribution);

        let values = grand_product.into_coeffs();
        assert!((values.len() + 1).is_power_of_two());
        let mut prepadded = Vec::with_capacity(values.len() + 1);
        prepadded.push(E::Fr::one());
        prepadded.extend(values);

        let z_2 = Polynomial::<E::Fr, Values>::from_values(prepadded)?;

        z_2
    };

    let z_1 = z_1.ifft(&worker);
    let z_2 = z_2.ifft(&worker);

    let (z_1_commitment, z_1_aux) = committer.commit_single(&z_1);
    let (z_2_commitment, z_2_aux) = committer.commit_single(&z_2);

    transcript.commit_input(&z_1_commitment);
    transcript.commit_input(&z_2_commitment);

    let mut z_1_shifted = z_1.clone();
    z_1_shifted.distribute_powers(&worker, z_1.omega);
    
    let mut z_2_shifted = z_2.clone();
    z_2_shifted.distribute_powers(&worker, z_2.omega);
    
    let a_lde = a_poly.clone().coset_lde(&worker, 4)?;
    let b_lde = b_poly.clone().coset_lde(&worker, 4)?;
    let c_lde = c_poly.clone().coset_lde(&worker, 4)?;

    let (q_l, q_r, q_o, q_m, q_c, s_id, sigma_1, sigma_2, sigma_3) = assembly.output_setup_polynomials(&worker)?;

    let q_l_lde = q_l.clone().coset_lde(&worker, 4)?;
    let q_r_lde = q_r.clone().coset_lde(&worker, 4)?;
    let q_o_lde = q_o.clone().coset_lde(&worker, 4)?;
    let q_m_lde = q_m.clone().coset_lde(&worker, 4)?;
    let q_c_lde = q_c.clone().coset_lde(&worker, 4)?;
    let s_id_lde = s_id.clone().coset_lde(&worker, 4)?;
    let sigma_1_lde = sigma_1.clone().coset_lde(&worker, 4)?;
    let sigma_2_lde = sigma_2.clone().coset_lde(&worker, 4)?;
    let sigma_3_lde = sigma_3.clone().coset_lde(&worker, 4)?;

    let n_fe = E::Fr::from_str(&n.to_string()).expect("must be valid field element");
    let mut two_n_fe = n_fe;
    two_n_fe.double();

    let alpha = transcript.get_challenge();

    let mut vanishing_poly_inverse = assembly.calculate_inverse_vanishing_polynomial_in_a_coset(&worker, q_c_lde.size(), required_domain_size.next_power_of_two())?;

    let mut t_1 = {
        let mut t_1 = q_c_lde;

        let mut q_l_by_a = q_l_lde;
        q_l_by_a.mul_assign(&worker, &a_lde);
        t_1.add_assign(&worker, &q_l_by_a);
        drop(q_l_by_a);

        let mut q_r_by_b = q_r_lde;
        q_r_by_b.mul_assign(&worker, &b_lde);
        t_1.add_assign(&worker, &q_r_by_b);
        drop(q_r_by_b);

        let mut q_o_by_c = q_o_lde;
        q_o_by_c.mul_assign(&worker, &c_lde);
        t_1.add_assign(&worker, &q_o_by_c);
        drop(q_o_by_c);

        let mut q_m_by_ab = q_m_lde;
        q_m_by_ab.mul_assign(&worker, &a_lde);
        q_m_by_ab.mul_assign(&worker, &b_lde);
        t_1.add_assign(&worker, &q_m_by_ab);
        drop(q_m_by_ab);

        vanishing_poly_inverse.scale(&worker, alpha);

        t_1.mul_assign(&worker, &vanishing_poly_inverse);

        t_1
    };

    let z_1_lde = z_1.clone().coset_lde(&worker, 4)?;

    let z_1_shifted_lde = z_1_shifted.clone().coset_lde(&worker, 4)?;

    let z_2_lde = z_2.clone().coset_lde(&worker, 4)?;

    let z_2_shifted_lde = z_2_shifted.clone().coset_lde(&worker, 4)?;

    {
        // TODO: May be optimize number of additions
        let mut contrib_z_1 = z_1_lde.clone();

        let mut s_id_by_beta = s_id_lde;
        s_id_by_beta.scale(&worker, beta);

        let mut n_by_beta = n_fe;
        n_by_beta.mul_assign(&beta);

        let mut a_perm = s_id_by_beta.clone();
        a_perm.add_constant(&worker, &gamma);
        a_perm.add_assign(&worker, &a_lde);
        contrib_z_1.mul_assign(&worker, &a_perm);
        drop(a_perm);

        s_id_by_beta.add_constant(&worker, &n_by_beta);

        let mut b_perm = s_id_by_beta.clone();

        b_perm.add_constant(&worker, &gamma);
        b_perm.add_assign(&worker, &b_lde);
        contrib_z_1.mul_assign(&worker, &b_perm);
        drop(b_perm);

        s_id_by_beta.add_constant(&worker, &n_by_beta);

        let mut c_perm = s_id_by_beta;
        c_perm.add_constant(&worker, &gamma);
        c_perm.add_assign(&worker, &c_lde);
        contrib_z_1.mul_assign(&worker, &c_perm);
        drop(c_perm);

        contrib_z_1.sub_assign(&worker, &z_1_shifted_lde);

        vanishing_poly_inverse.scale(&worker, alpha);

        contrib_z_1.mul_assign(&worker, &vanishing_poly_inverse);

        t_1.add_assign(&worker, &contrib_z_1);
    }

        {
        // TODO: May be optimize number of additions
        let mut contrib_z_2 = z_2_lde.clone();

        let mut a_perm = sigma_1_lde;
        a_perm.scale(&worker, beta);
        a_perm.add_constant(&worker, &gamma);
        a_perm.add_assign(&worker, &a_lde);
        contrib_z_2.mul_assign(&worker, &a_perm);
        drop(a_perm);


        let mut b_perm = sigma_2_lde;
        b_perm.scale(&worker, beta);
        b_perm.add_constant(&worker, &gamma);
        b_perm.add_assign(&worker, &b_lde);
        contrib_z_2.mul_assign(&worker, &b_perm);
        drop(b_perm);

        let mut c_perm = sigma_3_lde;
        c_perm.scale(&worker, beta);
        c_perm.add_constant(&worker, &gamma);
        c_perm.add_assign(&worker, &c_lde);
        contrib_z_2.mul_assign(&worker, &c_perm);
        drop(c_perm);

        contrib_z_2.sub_assign(&worker, &z_2_shifted_lde);

        vanishing_poly_inverse.scale(&worker, alpha);

        contrib_z_2.mul_assign(&worker, &vanishing_poly_inverse);

        t_1.add_assign(&worker, &contrib_z_2);
    }

    drop(a_lde);
    drop(b_lde);
    drop(c_lde);

    let l_0 = assembly.calculate_lagrange_poly(&worker, required_domain_size.next_power_of_two(), 0)?;
    let l_n_minus_one = assembly.calculate_lagrange_poly(&worker, required_domain_size.next_power_of_two(), n-1)?;

    {
        let mut z_1_minus_z_2_shifted = z_1_shifted_lde.clone();
        z_1_minus_z_2_shifted.sub_assign(&worker, &z_2_shifted_lde);

        let l = l_n_minus_one.clone().coset_lde(&worker, 4)?;

        z_1_minus_z_2_shifted.mul_assign(&worker, &l);
        drop(l);

        vanishing_poly_inverse.scale(&worker, alpha);

        z_1_minus_z_2_shifted.mul_assign(&worker, &vanishing_poly_inverse);

        t_1.add_assign(&worker, &z_1_minus_z_2_shifted);
    }

    {
        let mut z_1_minus_z_2= z_1_lde.clone();
        z_1_minus_z_2.sub_assign(&worker, &z_2_lde);

        let l = l_0.clone().coset_lde(&worker, 4)?;

        z_1_minus_z_2.mul_assign(&worker, &l);
        drop(l);

        vanishing_poly_inverse.scale(&worker, alpha);

        z_1_minus_z_2.mul_assign(&worker, &vanishing_poly_inverse);

        t_1.add_assign(&worker, &z_1_minus_z_2);
    }

    let t_poly = t_1.icoset_fft(&worker);

    let degree = get_degree::<E>(&t_poly);

    assert!(degree <= 3*n);
    
    fn get_degree<E:Engine>(poly: &Polynomial<E::Fr, Coefficients>) -> usize {
        let mut degree = poly.as_ref().len() - 1;
        for c in poly.as_ref().iter().rev() {
            if c.is_zero() {
                degree -= 1;
            } else {
                break;
            }
        }

        println!("Degree = {}", degree);

        degree
    }

    let (t_commitment, t_2_aux) = committer.commit_single(&t_poly);

    transcript.commit_input(&t_commitment);

    let z = transcript.get_challenge();

    // this is a sanity check

    let a_at_z = a_poly.evaluate_at(&worker, z);
    let b_at_z = b_poly.evaluate_at(&worker, z);
    let c_at_z = c_poly.evaluate_at(&worker, z);

    let q_l_at_z = q_l.evaluate_at(&worker, z);
    let q_r_at_z = q_r.evaluate_at(&worker, z);
    let q_o_at_z = q_o.evaluate_at(&worker, z);
    let q_m_at_z = q_m.evaluate_at(&worker, z);
    let q_c_at_z = q_c.evaluate_at(&worker, z);

    let s_id_at_z = s_id.evaluate_at(&worker, z);
    let sigma_1_at_z = sigma_1.evaluate_at(&worker, z);
    let sigma_2_at_z = sigma_2.evaluate_at(&worker, z);
    let sigma_3_at_z = sigma_3.evaluate_at(&worker, z);

    let mut inverse_vanishing_at_z = assembly.evaluate_inverse_vanishing_poly(required_domain_size.next_power_of_two(), z);

    let inverse_vanishing_at_z_no_alphas = inverse_vanishing_at_z;

    let z_1_at_z = z_1.evaluate_at(&worker, z);
    let z_2_at_z = z_2.evaluate_at(&worker, z);

    let z_1_shifted_at_z = z_1_shifted.evaluate_at(&worker, z);
    let z_2_shifted_at_z = z_2_shifted.evaluate_at(&worker, z);

    let l_0_at_z = l_0.evaluate_at(&worker, z);
    let l_n_minus_one_at_z = l_n_minus_one.evaluate_at(&worker, z);

    let t_at_z = t_poly.evaluate_at(&worker, z);

    {
        transcript.commit_field_element(&a_at_z);
        transcript.commit_field_element(&b_at_z);
        transcript.commit_field_element(&c_at_z);

        transcript.commit_field_element(&q_l_at_z);
        transcript.commit_field_element(&q_r_at_z);
        transcript.commit_field_element(&q_o_at_z);
        transcript.commit_field_element(&q_m_at_z);
        transcript.commit_field_element(&q_c_at_z);

        transcript.commit_field_element(&s_id_at_z);
        transcript.commit_field_element(&sigma_1_at_z);
        transcript.commit_field_element(&sigma_2_at_z);
        transcript.commit_field_element(&sigma_3_at_z);

        transcript.commit_field_element(&t_at_z);

        transcript.commit_field_element(&z_1_shifted_at_z);
        transcript.commit_field_element(&z_2_shifted_at_z);
    }

    let unshifted_opening_aggregation_challenge = transcript.get_challenge();

    let shifted_opening_aggregation_challenge = transcript.get_challenge();

    // this is a sanity check
    {
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

            inverse_vanishing_at_z.mul_assign(&alpha);

            res.mul_assign(&inverse_vanishing_at_z);

            res
        };

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

        assert_eq!(t_at_z, t_1);
    }

    // now compute linearization polynomial

    let mut r_1 = {
        let mut res = q_c;

        res.add_assign_scaled(&worker, &q_l, &a_at_z);
        res.add_assign_scaled(&worker, &q_r, &b_at_z);
        res.add_assign_scaled(&worker, &q_o, &c_at_z);

        let mut a_by_b_at_z = a_at_z;
        a_by_b_at_z.mul_assign(&b_at_z);
        res.add_assign_scaled(&worker, &q_m, &a_by_b_at_z);

        res.scale(&worker, alpha);

        res
    };

    {
        let mut factor = alpha;
        factor.square();

        let mut tmp = s_id_at_z;
        tmp.mul_assign(&beta);
        tmp.add_assign(&a_at_z);
        tmp.add_assign(&gamma);
        factor.mul_assign(&tmp);

        let mut tmp = s_id_at_z;
        tmp.add_assign(&n_fe);
        tmp.mul_assign(&beta);
        tmp.add_assign(&b_at_z);
        tmp.add_assign(&gamma);
        factor.mul_assign(&tmp);

        let mut tmp = s_id_at_z;
        tmp.add_assign(&two_n_fe);
        tmp.mul_assign(&beta);
        tmp.add_assign(&c_at_z);
        tmp.add_assign(&gamma);
        factor.mul_assign(&tmp);

        r_1.add_assign_scaled(&worker, &z_1, &factor);
    }

    {
        let mut factor = alpha;
        factor.square();
        factor.mul_assign(&alpha);

        let mut tmp = sigma_1_at_z;
        tmp.mul_assign(&beta);
        tmp.add_assign(&a_at_z);
        tmp.add_assign(&gamma);
        factor.mul_assign(&tmp);

        let mut tmp = sigma_2_at_z;
        tmp.mul_assign(&beta);
        tmp.add_assign(&b_at_z);
        tmp.add_assign(&gamma);
        factor.mul_assign(&tmp);

        let mut tmp = sigma_3_at_z;
        tmp.mul_assign(&beta);
        tmp.add_assign(&c_at_z);
        tmp.add_assign(&gamma);
        factor.mul_assign(&tmp);

        r_1.add_assign_scaled(&worker, &z_2, &factor);
    }

    {
        let mut factor = alpha;
        factor.square();
        factor.square();
        factor.mul_assign(&alpha);
        factor.mul_assign(&l_0_at_z);

        let mut tmp = z_1;
        tmp.sub_assign(&worker, &z_2);

        r_1.add_assign_scaled(&worker, &tmp, &factor);
    }

    let (r_commitment, r_aux_data) = committer.commit_single(&r_1);

    let r_at_z = r_1.evaluate_at(&worker, z);

    // another sanity check

    {
        let reevaluated_at_at_z = {
            let mut numerator = r_at_z;

            let mut tmp = alpha;
            tmp.square();
            tmp.mul_assign(&z_1_shifted_at_z);

            numerator.sub_assign(&tmp);

            let mut tmp = alpha;
            tmp.square();
            tmp.mul_assign(&alpha);
            tmp.mul_assign(&z_2_shifted_at_z);

            numerator.sub_assign(&tmp);

            let mut z_1_shifted_minus_z_2_shifted = z_1_shifted_at_z;
            z_1_shifted_minus_z_2_shifted.sub_assign(&z_2_shifted_at_z);

            let mut tmp = alpha;
            tmp.square();
            tmp.square();
            tmp.mul_assign(&l_n_minus_one_at_z);
            tmp.mul_assign(&z_1_shifted_minus_z_2_shifted);

            numerator.add_assign(&tmp);

            numerator.mul_assign(&inverse_vanishing_at_z_no_alphas);

            numerator
        };

        assert_eq!(t_at_z, reevaluated_at_at_z);

    }

    // follow the order from the paper

    let unshifted_opening_values = vec![t_at_z, r_at_z, a_at_z, b_at_z, c_at_z, ]

    Ok(())
}

#[cfg(test)]
mod test {

    use super::*;
    use crate::pairing::ff::{Field, PrimeField};
    use crate::pairing::{Engine};

    use crate::{SynthesisError};
    use std::marker::PhantomData;

    use crate::plonk::cs::gates::*;
    use crate::plonk::cs::*;

    struct TestCircuit<E:Engine>{
        _marker: PhantomData<E>
    }

    impl<E: Engine> Circuit<E> for TestCircuit<E> {
        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            let a = cs.alloc(|| {
                Ok(E::Fr::from_str("10").unwrap())
            })?;

            println!("A = {:?}", a);

            let b = cs.alloc(|| {
                Ok(E::Fr::from_str("20").unwrap())
            })?;

            println!("B = {:?}", b);

            let c = cs.alloc(|| {
                Ok(E::Fr::from_str("200").unwrap())
            })?;

            println!("C = {:?}", c);

            let one = E::Fr::one();

            let mut two = one;
            two.double();

            let mut negative_one = one;
            negative_one.negate();

            cs.enforce_zero_2((a, b), (two, negative_one))?;

            let ten = E::Fr::from_str("10").unwrap();
            cs.enforce_zero_2((b, c), (ten, negative_one))?;

            cs.enforce_mul_3((a, b, c))?;

            Ok(())
        }
    }

    #[test]
    fn test_trivial_circuit() {
        use crate::pairing::bn256::{Bn256, Fr};

        let mut assembly = GeneratorAssembly::<Bn256>::new();

        let circuit = TestCircuit::<Bn256> {
            _marker: PhantomData
        };

        circuit.synthesize(&mut assembly).expect("must work");

        println!("{:?}", assembly);

        assembly.finalize();

        let (f_l, f_r, f_o) = assembly.make_wire_assingments();

        let (sigma_1, sigma_2, sigma_3) = assembly.calculate_permutations_as_in_a_paper();

        let num_gates = assembly.num_gates();

        let id_1: Vec<_> = (1..=num_gates).collect();
        let id_2: Vec<_> = ((num_gates+1)..=(2*num_gates)).collect();
        let id_3: Vec<_> = ((2*num_gates + 1)..=(3*num_gates)).collect();

        let beta = Fr::from_str("15").unwrap();
        let gamma = Fr::from_str("4").unwrap();

        let mut f_1_poly = vec![];
        let mut g_1_poly = vec![];
        for (i, el) in f_l.iter().enumerate() {
            let mut tmp = Fr::from_str(&id_1[i].to_string()).unwrap();
            tmp.mul_assign(&beta);
            tmp.add_assign(&gamma);
            tmp.add_assign(&el);
            f_1_poly.push(tmp);
        }

        for (i, el) in f_l.iter().enumerate() {
            let mut tmp = Fr::from_str(&sigma_1[i].to_string()).unwrap();
            tmp.mul_assign(&beta);
            tmp.add_assign(&gamma);
            tmp.add_assign(&el);
            g_1_poly.push(tmp);
        }

        let mut f_2_poly = vec![];
        let mut g_2_poly = vec![];
        for (i, el) in f_r.iter().enumerate() {
            let mut tmp = Fr::from_str(&id_2[i].to_string()).unwrap();
            tmp.mul_assign(&beta);
            tmp.add_assign(&gamma);
            tmp.add_assign(&el);
            f_2_poly.push(tmp);
        }

        for (i, el) in f_r.iter().enumerate() {
            let mut tmp = Fr::from_str(&sigma_2[i].to_string()).unwrap();
            tmp.mul_assign(&beta);
            tmp.add_assign(&gamma);
            tmp.add_assign(&el);
            g_2_poly.push(tmp);
        }


        let mut f_3_poly = vec![];
        let mut g_3_poly = vec![];
        for (i, el) in f_o.iter().enumerate() {
            let mut tmp = Fr::from_str(&id_3[i].to_string()).unwrap();
            tmp.mul_assign(&beta);
            tmp.add_assign(&gamma);
            tmp.add_assign(&el);
            f_3_poly.push(tmp);
        }

        for (i, el) in f_o.iter().enumerate() {
            let mut tmp = Fr::from_str(&sigma_3[i].to_string()).unwrap();
            tmp.mul_assign(&beta);
            tmp.add_assign(&gamma);
            tmp.add_assign(&el);
            g_3_poly.push(tmp);
        }

        let mut f_poly = vec![];
        let mut g_poly = vec![];

        for i in 0..f_1_poly.len() {
            let mut tmp = f_1_poly[i];
            tmp.mul_assign(&f_2_poly[i]);
            tmp.mul_assign(&f_3_poly[i]);
            f_poly.push(tmp);
        }

        for i in 0..g_1_poly.len() {
            let mut tmp = g_1_poly[i];
            tmp.mul_assign(&g_2_poly[i]);
            tmp.mul_assign(&g_3_poly[i]);
            g_poly.push(tmp);
        }

        let mut tmp = Fr::one();
        let mut f_prime = vec![tmp];
        for el in f_poly.iter() {
            tmp.mul_assign(&el);
            f_prime.push(tmp);
        }

        let mut tmp = Fr::one();
        let mut g_prime = vec![tmp];
        for el in g_poly.iter() {
            tmp.mul_assign(&el);
            g_prime.push(tmp);
        }

        assert!(f_prime[0] == g_prime[0]);
        assert!(f_prime[num_gates] == g_prime[num_gates]);

        let worker = Worker::new();

        let _ = assembly.output_setup_polynomials(&worker).unwrap();

        let _ = assembly.generate_proof().unwrap();

    }

    #[test]
    fn test_coset_lde() {
        use crate::pairing::bn256::{Bn256, Fr};

        let worker = Worker::new();

        let coeffs: Vec<_> = (0..4).collect();
        let coeffs = convert_to_field_elements(&coeffs, &worker);
        let coeffs = Polynomial::<Fr, _>::from_coeffs(coeffs).unwrap();

        let mut expanded = coeffs.clone();
        expanded.pad_to_size(16).unwrap();

        let naive = expanded.coset_fft(&worker);
        let fast = coeffs.coset_lde(&worker, 4).unwrap();

        assert!(naive == fast);

    }
}