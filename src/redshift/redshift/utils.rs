use crate::SynthesisError;
use crate::pairing::ff::{Field, PrimeField};
use crate::pairing::{Engine};
use crate::multicore::*;
use std::convert::From;

use super::data_structures::*;
use super::gates::*;
use super::cs::*;

use crate::redshift::polynomials::*;
use crate::redshift::fft::cooley_tukey_ntt::*;
use crate::redshift::domains::*;
use crate::redshift::partial_reduction_field::PartialTwoBitReductionField;
use crate::redshift::IOP::FRI::coset_combining_fri::*;
use crate::redshift::IOP::oracle::*;
use crate::redshift::IOP::channel::*;

pub(crate) fn convert_to_field_elements<F: PrimeField>(indexes: &[usize], worker: &Worker) -> Vec<F> {
    let mut result = vec![F::zero(); indexes.len()];
    
    worker.scope(indexes.len(), |scope, chunk| {
        for (idx, fe) in indexes.chunks(chunk)
                .zip(result.chunks_mut(chunk)) {
            scope.spawn(move |_| {
                let mut repr = F::zero().into_repr();
                for (idx, fe) in idx.iter().zip(fe.iter_mut()) {
                    repr.as_mut()[0] = *idx as u64;
                    *fe = F::from_repr(repr).expect("is a valid representation");
                }
            });
        }
    });

    result
}

pub(crate) fn commit_single_poly<E: Engine, CP: CTPrecomputations<E::Fr>, I: Oracle<E::Fr>>(
        poly: &Polynomial<E::Fr, Coefficients>,
        deg: usize, 
        omegas_bitreversed: &CP,
        params: &FriParams,
        worker: &Worker
    ) -> Result<SinglePolyCommitmentData<E::Fr, I>, SynthesisError> 
where E::Fr : PartialTwoBitReductionField {
    let lde = poly.clone().bitreversed_lde_using_bitreversed_ntt_with_partial_reduction(
        worker, 
        params.lde_factor, 
        omegas_bitreversed, 
        &E::Fr::multiplicative_generator()
    )?;

    let oracle_params = I::Params::from(1 << params.collapsing_factor);
    let oracle = I::create(&lde.as_ref(), &oracle_params);

    Ok(SinglePolyCommitmentData::<E::Fr, _> {
        poly: lde,
        deg,
        oracle: oracle
    })
}

pub(crate) fn calculate_permutations_as_in_a_paper<E: Engine>(
    input_gates: &Vec<Gate<E::Fr>>,
    aux_gates: &Vec<Gate<E::Fr>>,
    num_inputs: &usize,
    num_aux: &usize,
) -> (Vec<usize>, Vec<usize>, Vec<usize>) 
{
    let num_gates = input_gates.len() + aux_gates.len();
    let num_partitions = num_inputs + num_aux;
    // in the partition number i there is a set of indexes in V = (a, b, c) such that V_j = i
    let mut partitions = vec![vec![]; num_partitions + 1];

    for (j, gate) in input_gates.iter().chain(aux_gates).enumerate()
    {
        match gate.a_wire() {
            Variable(Index::Input(index)) => {
                let i = *index;
                partitions[i].push(j+1);
            },
            Variable(Index::Aux(index)) => {
                if *index != 0 {
                    let i = index + num_inputs;
                    partitions[i].push(j+1);
                }
            },
        }

        match gate.b_wire() {
            Variable(Index::Input(index)) => {
                let i = *index;
                partitions[i].push(j + 1 + num_gates);
            },
            Variable(Index::Aux(index)) => {
                if *index != 0 {
                    let i = index + num_inputs;
                    partitions[i].push(j + 1 + num_gates);
                }
            },
        }

        match gate.c_wire() {
            Variable(Index::Input(index)) => {
                let i = *index;
                partitions[i].push(j + 1 + 2*num_gates);
            },
            Variable(Index::Aux(index)) => {
                if *index != 0 {
                    let i = index + num_inputs;
                    partitions[i].push(j + 1 + 2*num_gates);
                }
            },
        }
    }

    let mut sigma_1: Vec<_> = (1..=num_gates).collect();
    let mut sigma_2: Vec<_> = ((num_gates+1)..=(2*num_gates)).collect();
    let mut sigma_3: Vec<_> = ((2*num_gates + 1)..=(3*num_gates)).collect();

    let mut permutations = vec![vec![]; num_partitions + 1];

    fn rotate(mut vec: Vec<usize>) -> Vec<usize> {
        if vec.len() > 0 {
            let els: Vec<_> = vec.drain(0..1).collect();
            vec.push(els[0]);
        }

        vec
    }

    for (i, partition) in partitions.into_iter().enumerate().skip(1) {
        // copy-permutation should have a cycle around the partition

        let permutation = rotate(partition.clone());
        permutations[i] = permutation.clone();

        for (original, new) in partition.into_iter()
                                .zip(permutation.into_iter()) 
        {
            if original <= num_gates {
                debug_assert!(sigma_1[original - 1] == original);
                sigma_1[original - 1] = new;
            } else if original <= 2*num_gates {
                debug_assert!(sigma_2[original - num_gates - 1] == original);
                sigma_2[original - num_gates - 1] = new;
            } else {
                debug_assert!(sigma_3[original - 2*num_gates - 1] == original);
                sigma_3[original - 2*num_gates - 1] = new;
            }
        }
    }

    (sigma_1, sigma_2, sigma_3)
}

fn make_s_id<E: Engine>(input_gates: &Vec<Gate<E::Fr>>, aux_gates: &Vec<Gate<E::Fr>>) -> Vec<usize> {

    let size = input_gates.len() + aux_gates.len();
    let result: Vec<_> = (1..=size).collect();

    result
}

pub(crate) fn make_circuit_description_polynomials<E: Engine>(
    input_gates: &Vec<Gate<E::Fr>>,
    aux_gates: &Vec<Gate<E::Fr>>,
    _num_inputs: &usize,
    _num_aux: &usize,
    worker: &Worker) -> Result<(
        Polynomial::<E::Fr, Values>, Polynomial::<E::Fr, Values>, Polynomial::<E::Fr, Values>,
        Polynomial::<E::Fr, Values>, Polynomial::<E::Fr, Values>, Polynomial::<E::Fr, Values>
    ), SynthesisError> 
{

    let total_num_gates = input_gates.len() + aux_gates.len();
    let mut q_l = vec![E::Fr::zero(); total_num_gates];
    let mut q_r = vec![E::Fr::zero(); total_num_gates];
    let mut q_o = vec![E::Fr::zero(); total_num_gates];
    let mut q_m = vec![E::Fr::zero(); total_num_gates];
    let mut q_c = vec![E::Fr::zero(); total_num_gates];
    //short from additonal selector
    let mut q_add_sel = vec![E::Fr::zero(); total_num_gates];

    // expect a small number of inputs
    for ((((((gate, q_l), q_r), q_o), q_m), q_c), q_add_sel) in input_gates.iter()
                                        .zip(q_l.iter_mut())
                                        .zip(q_r.iter_mut())
                                        .zip(q_o.iter_mut())
                                        .zip(q_m.iter_mut())
                                        .zip(q_c.iter_mut())
                                        .zip(q_add_sel.iter_mut())
    {
        *q_l = gate.q_l().unpack();
        *q_r = gate.q_r().unpack();
        *q_o = gate.q_o().unpack();
        *q_m = gate.q_m().unpack();
        *q_c = gate.q_c().unpack();
        *q_add_sel = gate.q_add_sel().unpack();
    }

    let num_input_gates = input_gates.len();
    let q_l_aux = &mut q_l[num_input_gates..];
    let q_r_aux = &mut q_r[num_input_gates..];
    let q_o_aux = &mut q_o[num_input_gates..];
    let q_m_aux = &mut q_m[num_input_gates..];
    let q_c_aux = &mut q_c[num_input_gates..];
    let q_add_sel_aux = &mut q_add_sel[num_input_gates..];

    debug_assert!(aux_gates.len() == q_l_aux.len());

    worker.scope(aux_gates.len(), |scope, chunk| {
        for ((((((gate, q_l), q_r), q_o), q_m), q_c), q_add_sel) in aux_gates.chunks(chunk)
                                                        .zip(q_l_aux.chunks_mut(chunk))
                                                        .zip(q_r_aux.chunks_mut(chunk))
                                                        .zip(q_o_aux.chunks_mut(chunk))
                                                        .zip(q_m_aux.chunks_mut(chunk))
                                                        .zip(q_c_aux.chunks_mut(chunk))
                                                        .zip(q_add_sel_aux.chunks_mut(chunk))
        {
            scope.spawn(move |_| {
                for ((((((gate, q_l), q_r), q_o), q_m), q_c), q_add_sel) in gate.iter()
                                                        .zip(q_l.iter_mut())
                                                        .zip(q_r.iter_mut())
                                                        .zip(q_o.iter_mut())
                                                        .zip(q_m.iter_mut())
                                                        .zip(q_c.iter_mut())
                                                        .zip(q_add_sel.iter_mut())
                    {
                        *q_l = gate.q_l().unpack();
                        *q_r = gate.q_r().unpack();
                        *q_o = gate.q_o().unpack();
                        *q_m = gate.q_m().unpack();
                        *q_c = gate.q_c().unpack();
                        *q_add_sel = gate.q_add_sel().unpack();
                    }
            });
        }
    });

    let q_l = Polynomial::from_values(q_l)?;
    let q_r = Polynomial::from_values(q_r)?;
    let q_o = Polynomial::from_values(q_o)?;
    let q_m = Polynomial::from_values(q_m)?;
    let q_c = Polynomial::from_values(q_c)?;
    let q_add_sel = Polynomial::from_values(q_add_sel)?;

    Ok((q_l, q_r, q_o, q_m, q_c, q_add_sel))
}

pub(crate) fn output_setup_polynomials<E: Engine>(
    input_gates: &Vec<Gate<E::Fr>>,
    aux_gates: &Vec<Gate<E::Fr>>,
    num_inputs: &usize,
    num_aux: &usize,
    worker: &Worker) -> Result<
    (
        Polynomial::<E::Fr, Coefficients>, // q_l
        Polynomial::<E::Fr, Coefficients>, // q_r
        Polynomial::<E::Fr, Coefficients>, // q_o
        Polynomial::<E::Fr, Coefficients>, // q_m
        Polynomial::<E::Fr, Coefficients>, // q_c
        Polynomial::<E::Fr, Coefficients>, // q_add_sel
        Polynomial::<E::Fr, Coefficients>, // s_id
        Polynomial::<E::Fr, Coefficients>, // sigma_1
        Polynomial::<E::Fr, Coefficients>, // sigma_2
        Polynomial::<E::Fr, Coefficients>, // sigma_3
    ), SynthesisError> 
{
    let s_id = make_s_id::<E>(input_gates, aux_gates);
    let (sigma_1, sigma_2, sigma_3) = 
        calculate_permutations_as_in_a_paper::<E>(input_gates, aux_gates, num_inputs, num_aux);

    let s_id = convert_to_field_elements::<E::Fr>(&s_id, &worker);
    let sigma_1 = convert_to_field_elements::<E::Fr>(&sigma_1, &worker);
    let sigma_2 = convert_to_field_elements::<E::Fr>(&sigma_2, &worker);
    let sigma_3 = convert_to_field_elements::<E::Fr>(&sigma_3, &worker);

    let s_id = Polynomial::from_values(s_id)?;
    let sigma_1 = Polynomial::from_values(sigma_1)?;
    let sigma_2 = Polynomial::from_values(sigma_2)?;
    let sigma_3 = Polynomial::from_values(sigma_3)?;

    let (q_l, q_r, q_o, q_m, q_c, q_add_sel) = 
        make_circuit_description_polynomials::<E>(input_gates, aux_gates, num_inputs, num_aux, &worker)?;

    let s_id = s_id.ifft(&worker);
    let sigma_1 = sigma_1.ifft(&worker);
    let sigma_2 = sigma_2.ifft(&worker);
    let sigma_3 = sigma_3.ifft(&worker);

    let q_l = q_l.ifft(&worker);
    let q_r = q_r.ifft(&worker);
    let q_o = q_o.ifft(&worker);
    let q_m = q_m.ifft(&worker);
    let q_c = q_c.ifft(&worker);
    let q_add_sel = q_add_sel.ifft(&worker);

    Ok((q_l, q_r, q_o, q_m, q_c, q_add_sel, s_id, sigma_1, sigma_2, sigma_3))
}

pub(crate) fn multiopening<E: Engine, P: FriPrecomputations<E::Fr>, I: Oracle<E::Fr>, C: Channel<E::Fr, Input = I::Commitment>>
    ( 
        single_point_opening_requests: Vec<SinglePointOpeningRequest<E::Fr>>,
        double_point_opening_requests: Vec<DoublePointOpeningRequest<E::Fr>>,
        common_deg: usize,
        omegas_inv_bitreversed: &P,
        params: &FriParams,
        worker: &Worker,
        channel: &mut C,
    ) -> Result<(FriProofPrototype<E::Fr, I>), SynthesisError> 
where E::Fr : PartialTwoBitReductionField
{
    //we assert that all of the polynomials are of the same degree
    // TODO: deal with the case of various degrees
    let required_divisor_size = deg * params.lde_factor;

    // TODO: however after division all of the polynomials are of different and distinct degrees. How to hadne this?

    // Here we exploit the fact that we open only at omega and g * omega
    // we divide the polynomials in the groups by the same common values

    let mut final_aggregate = Polynomial::from_values(vec![E::Fr::zero(); required_divisor_size])?;

    let mut precomputed_bitreversed_coset_divisor = Polynomial::from_values(vec![E::Fr::one(); required_divisor_size])?;
    precomputed_bitreversed_coset_divisor.distribute_powers(&worker, precomputed_bitreversed_coset_divisor.omega);
    precomputed_bitreversed_coset_divisor.scale(&worker, E::Fr::multiplicative_generator());
    precomputed_bitreversed_coset_divisor.bitreverse_enumeration(&worker);

    let mut scratch_space_numerator = final_aggregate.clone();
    let mut scratch_space_denominator = final_aggregate.clone();

    let aggregation_challenge = channel.produce_field_element_challenge();
    let mut alpha = E::Fr::one();

    for request in single_point_opening_requests.iter() {
        let z = request.opening_point;
        let mut minus_z = z;
        minus_z.negate();
        scratch_space_denominator.reuse_allocation(&precomputed_bitreversed_coset_divisor);
        scratch_space_denominator.add_constant(&worker, &minus_z);
        scratch_space_denominator.batch_inversion(&worker)?;
        for (poly, value) in request.polynomials.iter().zip(request.opening_values.iter()) {
            scratch_space_numerator.reuse_allocation(&poly);
            let mut v = *value;
            v.negate();
            scratch_space_numerator.add_constant(&worker, &v);
            scratch_space_numerator.mul_assign(&worker, &scratch_space_denominator);
            if alpha != E::Fr::one() {
                scratch_space_numerator.scale(&worker, alpha);
            }

            final_aggregate.add_assign(&worker, &scratch_space_numerator);

            alpha.mul_assign(&aggregation_challenge);
        }
    }

    for request in double_point_opening_requests.iter() {
        // (omega - y)(omega - z) = omega^2 - (z+y)*omega + zy
        
        let setup_point = request.first_opening_point;
        let opening_point = request.second_opening_point;

        let mut t0 = setup_point;
        t0.add_assign(&opening_point);
        t0.negate();

        let mut t1 = setup_point;
        t1.mul_assign(&opening_point);

        scratch_space_denominator.reuse_allocation(&precomputed_bitreversed_coset_divisor);
        worker.scope(scratch_space_denominator.as_ref().len(), |scope, chunk| {
            for den in scratch_space_denominator.as_mut().chunks_mut(chunk) {
                scope.spawn(move |_| {
                    for d in den.iter_mut() {
                        let mut result = *d;
                        result.square();
                        result.add_assign(&t1);

                        let mut tmp = t0;
                        tmp.mul_assign(&d);

                        result.add_assign(&tmp);

                        *d = result;
                    }
                });
            }
        });

        scratch_space_denominator.batch_inversion(&worker)?;

        // each numerator must have a value removed of the polynomial that interpolates the following points:
        // (x, y)
        // (opening_x, opening_y)
        // such polynomial is linear and has a form: 
        // f(t) = opening_x + (t - x) * (opening_y - opening_x) / (y - x)
        // note that y and x should be distinct!

        for ((poly, setup_value), value) in request.polynomials.iter().zip(request.first_opening_values.iter()).zip(request.second_opening_values.iter()) {
            scratch_space_numerator.reuse_allocation(&poly);

            let intercept = setup_value;
                    let mut t0 = opening_point;
                    t0.sub_assign(&setup_point);

                    let mut slope = t0.inverse().expect("must exist");
                    
                    let mut t1 = *value;
                    t1.sub_assign(&setup_value);

                    slope.mul_assign(&t1);

                    worker.scope(scratch_space_numerator.as_ref().len(), |scope, chunk| {
                        for (num, omega) in scratch_space_numerator.as_mut().chunks_mut(chunk).
                                    zip(precomputed_bitreversed_coset_divisor.as_ref().chunks(chunk)) {
                            scope.spawn(move |_| {
                                for (n, omega) in num.iter_mut().zip(omega.iter()) {
                                    let mut result = *omega;
                                    result.sub_assign(&setup_point);
                                    result.mul_assign(&slope);
                                    result.add_assign(&intercept);

                                    n.sub_assign(&result);
                                }
                            });
                        }
                    });

                    scratch_space_numerator.mul_assign(&worker, &scratch_space_denominator);
                    if aggregation_challenge != E::Fr::one() {
                        scratch_space_numerator.scale(&worker, alpha);
                    }

                    final_aggregate.add_assign(&worker, &scratch_space_numerator);

                    alpha.mul_assign(&aggregation_challenge);
                }
            }

    let fri_prototype = FriIop::proof_from_lde(
        &final_aggregate,
        omegas_inv_bitreversed,
        &worker,
        &mut channel,
        &params,
    );

    fri_prototype
}

pub(crate) fn calculate_inverse_vanishing_polynomial_in_a_coset<E: Engine>(
    worker: &Worker, 
    poly_size:usize, 
    vahisning_size: usize
    ) -> Result<Polynomial::<E::Fr, Values>, SynthesisError> 
{
    assert!(poly_size.is_power_of_two());
    assert!(vahisning_size.is_power_of_two());

    // update from the paper - it should not hold for the last generator, omega^(n) in original notations

    // Z(X) = (X^(n+1) - 1) / (X - omega^(n)) => Z^{-1}(X) = (X - omega^(n)) / (X^(n+1) - 1)

    let domain = Domain::<E::Fr>::new_for_size(vahisning_size as u64)?;
    let n_domain_omega = domain.generator;
    let mut root = n_domain_omega.pow([(vahisning_size - 1) as u64]);
    root.negate();

    let multiplicative_generator = E::Fr::multiplicative_generator();

    let mut negative_one = E::Fr::one();
    negative_one.negate();

    let mut numerator = Polynomial::<E::Fr, Values>::from_values(vec![multiplicative_generator; poly_size])?;
    // evaluate X in linear time

    numerator.distribute_powers(&worker, numerator.omega);
    numerator.add_constant(&worker, &root);

    // numerator.add_constant(&worker, &negative_one);
    // now it's a series of values in a coset

    // now we should evaluate X^(n+1) - 1 in a linear time

    let shift = multiplicative_generator.pow([vahisning_size as u64]);
    
    let mut denominator = Polynomial::<E::Fr, Values>::from_values(vec![shift; poly_size])?;

    // elements are h^size - 1, (hg)^size - 1, (hg^2)^size - 1, ...

    denominator.distribute_powers(&worker, denominator.omega.pow([vahisning_size as u64]));
    denominator.add_constant(&worker, &negative_one);

    denominator.batch_inversion(&worker)?;

    numerator.mul_assign(&worker, &denominator);

    Ok(numerator)
}

pub(crate) fn evaluate_inverse_vanishing_poly<E: Engine>(vahisning_size: usize, point: E::Fr) -> E::Fr {
    assert!(vahisning_size.is_power_of_two());

    // update from the paper - it should not hold for the last generator, omega^(n) in original notations

    // Z(X) = (X^(n+1) - 1) / (X - omega^(n)) => Z^{-1}(X) = (X - omega^(n)) / (X^(n+1) - 1)

    let domain = Domain::<E::Fr>::new_for_size(vahisning_size as u64).expect("should fit");
    let n_domain_omega = domain.generator;
    let root = n_domain_omega.pow([(vahisning_size - 1) as u64]);

    let mut numerator = point;
    numerator.sub_assign(&root);

    let mut denominator = point.pow([vahisning_size as u64]);
    denominator.sub_assign(&E::Fr::one());

    let denominator = denominator.inverse().expect("must exist");

    numerator.mul_assign(&denominator);

    numerator
}

pub(crate) fn calculate_lagrange_poly<E: Engine>(worker: &Worker, poly_size:usize, poly_number: usize) 
    -> Result<Polynomial::<E::Fr, Coefficients>, SynthesisError> {
    assert!(poly_size.is_power_of_two());
    assert!(poly_number < poly_size);

    let mut poly = Polynomial::<E::Fr, Values>::from_values(vec![E::Fr::zero(); poly_size])?;

    poly.as_mut()[poly_number] = E::Fr::one();

    Ok(poly.ifft(&worker))
}