use crate::plonk::commitments::transparent::iop_compiler::coset_combining_blake2s_tree::*;
use crate::SynthesisError;
use crate::plonk::transparent_engine::PartialTwoBitReductionField;
use crate::pairing::ff::{Field, PrimeField};
use crate::pairing::{Engine};
use crate::plonk::commitments::transparent::iop_compiler::*;
use crate::plonk::polynomials::*;
use super::data_structures::*;
use crate::plonk::commitments::transparent::fri::coset_combining_fri::fri::*;
use crate::plonk::fft::cooley_tukey_ntt::*;
use crate::multicore::*;
use super::gates::*;

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

pub(crate) fn commit_single_poly<E: Engine, CP: CTPrecomputations<E::Fr>>(
        poly: &Polynomial<E::Fr, Coefficients>, 
        omegas_bitreversed: &CP,
        params: &RedshiftParameters<E::Fr>,
        worker: &Worker
    ) -> Result<SinglePolyCommitmentData<E::Fr, FriSpecificBlake2sTree<E::Fr>>, SynthesisError> 
where E::Fr : PartialTwoBitReductionField {
    let lde = poly.clone().bitreversed_lde_using_bitreversed_ntt_with_partial_reduction(
        worker, 
        params.lde_factor, 
        omegas_bitreversed, 
        &E::Fr::multiplicative_generator()
    )?;

    let oracle_params = FriSpecificBlake2sTreeParams {
        values_per_leaf: (1 << params.coset_params.cosets_schedule[0])
    };

    let oracle = FriSpecificBlake2sTree::create(&lde.as_ref(), &oracle_params);

    Ok(SinglePolyCommitmentData::<E::Fr, _> {
        poly: lde,
        oracle: oracle
    })
}

pub(crate) fn calculate_permutations_as_in_a_paper<E: Engine>(
    input_gates: &Vec<Gate<E::Fr>>,
    aux_gates: &Vec<Gate<E::Fr>>,
    num_inputs: usize,
    num_aux: usize,
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
    num_inputs: usize,
    num_aux: usize,
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
    num_inputs: usize,
    num_aux: usize,
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
        make_circuit_description_polynomials(input_gates, aux_gates, num_inputs, num_aux, &worker)?;

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