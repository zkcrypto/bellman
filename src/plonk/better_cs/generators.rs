use crate::pairing::ff::{Field, PrimeField};
use crate::pairing::{Engine};

use crate::{SynthesisError};
use std::marker::PhantomData;
use super::cs::*;
use crate::multicore::*;

use crate::plonk::polynomials::*;
use crate::plonk::domains::*;
use crate::plonk::utils::*;

use super::gates::*;
use super::data_structures::*;

#[derive(Debug)]
struct GeneratorAssembly<E: Engine> {
    m: usize,
    n: usize,
    input_gates: Vec<Gate<E::Fr>>,
    aux_gates: Vec<Gate<E::Fr>>,

    num_inputs: usize,
    num_aux: usize,

    is_finalized: bool,
}

impl<E: Engine> ConstraintSystem<E> for GeneratorAssembly<E> {
    // allocate a variable
    fn alloc<F>(&mut self, _value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError> 
    {
        self.num_aux += 1;
        let index = self.num_aux;

        Ok(Variable(Index::Aux(index)))
    }

    // allocate an input variable
    fn alloc_input<F>(&mut self, _value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError> 
    {
        self.num_inputs += 1;
        let index = self.num_inputs;
        let input_var = Variable(Index::Input(index));
        let zero = E::Fr::zero();
        let gate_coeffs = (E::Fr::one(), zero, zero, zero, zero, zero);
        let dummy = self.get_dummy_variable();
        let gate = Gate::<E::Fr>::new_gate((input_var, dummy, dummy), gate_coeffs);
        self.input_gates.push(gate);
        Ok(input_var)
    }

    // allocate an abstract gate
    fn new_gate(&mut self, variables: (Variable, Variable, Variable), 
        coeffs:(E::Fr, E::Fr, E::Fr, E::Fr, E::Fr, E::Fr)) -> Result<(), SynthesisError>
    {
        let gate = Gate::<E::Fr>::new_gate(variables, coeffs);
        self.aux_gates.push(gate);
        self.n += 1;

        Ok(())
    }

    fn get_dummy_variable(&self) -> Variable {
        self.dummy_variable()
    }
}

impl<E: Engine> GeneratorAssembly<E> {
    fn new_empty_gate(&mut self) -> usize {
        self.n += 1;
        let index = self.n;

        self.aux_gates.push(Gate::<E::Fr>::empty());

        index
    }

    fn set_gate(&mut self, gate: Gate<E::Fr>, index: usize) {
        self.aux_gates[index-1] = gate;
    }

    // allocate a constant
    fn enforce_constant(&mut self, variable: Variable, constant: E::Fr) -> Result<(), SynthesisError>
    {
        let gate = Gate::<E::Fr>::new_enforce_constant_gate(variable, Some(constant), self.dummy_variable());
        self.aux_gates.push(gate);
        self.n += 1;

        Ok(())
    }

    pub(crate) fn new() -> Self {
        let mut tmp = Self {
            n: 0,
            m: 0,
            input_gates: vec![],
            aux_gates: vec![],

            num_inputs: 0,
            num_aux: 0,

            is_finalized: false,
        };

        let zero = tmp.alloc(|| Ok(E::Fr::zero())).expect("should have no issues");
        tmp.enforce_constant(zero, E::Fr::zero()).expect("should have no issues");

        let one = tmp.alloc(|| Ok(E::Fr::one())).expect("should have no issues");
        tmp.enforce_constant(one, E::Fr::one()).expect("should have no issues");

        match (tmp.dummy_variable(), zero) {
            (Variable(Index::Aux(1)), Variable(Index::Aux(1))) => {},
            _ => panic!("zero variable is incorrect")
        }

        tmp
    }

    // return variable that is not in a constraint formally, but has some value
    fn dummy_variable(&self) -> Variable {
        // <Self as ConstraintSystem<E>>::ZERO
        Variable(Index::Aux(1))
    }

    pub(crate) fn make_circuit_description_polynomials(&self, worker: &Worker) -> Result<(
        Polynomial::<E::Fr, Values>, Polynomial::<E::Fr, Values>, Polynomial::<E::Fr, Values>,
        Polynomial::<E::Fr, Values>, Polynomial::<E::Fr, Values>, Polynomial::<E::Fr, Values>
    ), SynthesisError> {
        assert!(self.is_finalized);
        let total_num_gates = self.input_gates.len() + self.aux_gates.len();
        let mut q_l = vec![E::Fr::zero(); total_num_gates];
        let mut q_r = vec![E::Fr::zero(); total_num_gates];
        let mut q_o = vec![E::Fr::zero(); total_num_gates];
        let mut q_m = vec![E::Fr::zero(); total_num_gates];
        let mut q_c = vec![E::Fr::zero(); total_num_gates];
        //short from additonal selector
        let mut q_add_sel = vec![E::Fr::zero(); total_num_gates];

        fn coeff_into_field_element<F: PrimeField>(coeff: &Coeff<F>) -> F {
            match coeff {
                Coeff::Zero => {
                    F::zero()
                },
                Coeff::One => {
                    F::one()
                },
                Coeff::NegativeOne => {
                    let mut tmp = F::one();
                    tmp.negate();

                    tmp
                },
                Coeff::Full(c) => {
                    *c
                },
            }
        }

        // expect a small number of inputs
        for ((((((gate, q_l), q_r), q_o), q_m), q_c), q_add_sel) in self.input_gates.iter()
                                            .zip(q_l.iter_mut())
                                            .zip(q_r.iter_mut())
                                            .zip(q_o.iter_mut())
                                            .zip(q_m.iter_mut())
                                            .zip(q_c.iter_mut())
                                            .zip(q_add_sel.iter_mut())
        {
            *q_l = coeff_into_field_element::<E::Fr>(&gate.q_l());
            *q_r = coeff_into_field_element::<E::Fr>(&gate.q_r());
            *q_o = coeff_into_field_element::<E::Fr>(&gate.q_o());
            *q_m = coeff_into_field_element::<E::Fr>(&gate.q_m());
            *q_c = coeff_into_field_element::<E::Fr>(&gate.q_c());
            *q_add_sel = coeff_into_field_element::<E::Fr>(&gate.q_add_sel());
        }


        let num_input_gates = self.input_gates.len();
        let q_l_aux = &mut q_l[num_input_gates..];
        let q_r_aux = &mut q_r[num_input_gates..];
        let q_o_aux = &mut q_o[num_input_gates..];
        let q_m_aux = &mut q_m[num_input_gates..];
        let q_c_aux = &mut q_c[num_input_gates..];
        let q_add_sel_aux = &mut q_add_sel[num_input_gates..];

        debug_assert!(self.aux_gates.len() == q_l_aux.len());

        worker.scope(self.aux_gates.len(), |scope, chunk| {
            for ((((((gate, q_l), q_r), q_o), q_m), q_c), q_add_sel) in self.aux_gates.chunks(chunk)
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
                            *q_l = coeff_into_field_element(&gate.q_l());
                            *q_r = coeff_into_field_element(&gate.q_r());
                            *q_o = coeff_into_field_element(&gate.q_o());
                            *q_m = coeff_into_field_element(&gate.q_m());
                            *q_c = coeff_into_field_element(&gate.q_c());
                            *q_add_sel = coeff_into_field_element(&gate.q_add_sel());
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

    pub(crate) fn calculate_permutations_as_in_a_paper(&self) -> (Vec<usize>, Vec<usize>, Vec<usize>) {
        assert!(self.is_finalized);

        let num_gates = self.input_gates.len() + self.aux_gates.len();
        let num_partitions = self.num_inputs + self.num_aux;
        let num_inputs = self.num_inputs;
        // in the partition number i there is a set of indexes in V = (a, b, c) such that V_j = i
        let mut partitions = vec![vec![]; num_partitions + 1];

        for (j, gate) in self.input_gates.iter().chain(&self.aux_gates).enumerate()
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

    fn make_s_id(&self) -> Vec<usize> {
        assert!(self.is_finalized);

        let size = self.input_gates.len() + self.aux_gates.len();
        let result: Vec<_> = (1..=size).collect();

        result
    }

    pub(crate) fn output_setup_polynomials(&self, worker: &Worker) -> Result<
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
        assert!(self.is_finalized);

        let s_id = self.make_s_id();
        let (sigma_1, sigma_2, sigma_3) = self.calculate_permutations_as_in_a_paper();

        let s_id = convert_to_field_elements::<E::Fr>(&s_id, &worker);
        let sigma_1 = convert_to_field_elements::<E::Fr>(&sigma_1, &worker);
        let sigma_2 = convert_to_field_elements::<E::Fr>(&sigma_2, &worker);
        let sigma_3 = convert_to_field_elements::<E::Fr>(&sigma_3, &worker);

        let s_id = Polynomial::from_values(s_id)?;
        let sigma_1 = Polynomial::from_values(sigma_1)?;
        let sigma_2 = Polynomial::from_values(sigma_2)?;
        let sigma_3 = Polynomial::from_values(sigma_3)?;

        let (q_l, q_r, q_o, q_m, q_c, q_add_sel) = self.make_circuit_description_polynomials(&worker)?;

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

    pub(crate) fn num_gates(&self) -> usize {
        self.input_gates.len() + self.aux_gates.len()
    }

    fn finalize(&mut self) {
        if self.is_finalized {
            return;
        }

        let n = self.input_gates.len() + self.aux_gates.len();
        if (n+1).is_power_of_two() {
            self.is_finalized = true;
            return;
        }

        let empty_gate = Gate::<E::Fr>::new_empty_gate(self.dummy_variable());

        let new_aux_len = (n+1).next_power_of_two() - 1 - self.input_gates.len();

        self.aux_gates.resize(new_aux_len, empty_gate);

        let n = self.input_gates.len() + self.aux_gates.len();
        assert!((n+1).is_power_of_two());

        self.is_finalized = true;
    }
}

pub fn setup_with_precomputations<E: Engine, C: Circuit<E>, CP: CTPrecomputations<E::Fr>, T: Transcript<E::Fr, Input = <FriSpecificBlake2sTree<E::Fr> as IopInstance<E::Fr>> :: Commitment> >(
    circuit: &C,
    params: &RedshiftParameters<E::Fr>,
    omegas_bitreversed: &CP,
    ) -> Result<(RedshiftSetup<E::Fr, FriSpecificBlake2sTree<E::Fr>>, RedshiftSetupPrecomputation<E::Fr, FriSpecificBlake2sTree<E::Fr>>), SynthesisError> 
        where E::Fr : PartialTwoBitReductionField 
{
    let mut assembly = GeneratorAssembly::<E>::new();
    circuit.synthesize(&mut assembly)?;
    assembly.finalize();
    
    let n = assembly.num_gates();

    let worker = Worker::new();

    let mut transcript = T::new();

    let (q_l, q_r, q_o, q_m, q_c, s_id, sigma_1, sigma_2, sigma_3) = assembly.output_setup_polynomials(&worker)?;

    let q_l_commitment_data = ProvingAssembly::<E>::commit_single_poly(&q_l, omegas_bitreversed, &params, &worker)?;
    let q_r_commitment_data = ProvingAssembly::<E>::commit_single_poly(&q_r, omegas_bitreversed, &params, &worker)?;
    let q_o_commitment_data = ProvingAssembly::<E>::commit_single_poly(&q_o, omegas_bitreversed, &params, &worker)?;
    let q_m_commitment_data = ProvingAssembly::<E>::commit_single_poly(&q_m, omegas_bitreversed, &params, &worker)?;
    let q_c_commitment_data = ProvingAssembly::<E>::commit_single_poly(&q_c, omegas_bitreversed, &params, &worker)?;
    let s_id_commitment_data = ProvingAssembly::<E>::commit_single_poly(&s_id, omegas_bitreversed, &params, &worker)?;
    let sigma_1_commitment_data = ProvingAssembly::<E>::commit_single_poly(&sigma_1, omegas_bitreversed, &params, &worker)?;
    let sigma_2_commitment_data = ProvingAssembly::<E>::commit_single_poly(&sigma_2, omegas_bitreversed, &params, &worker)?;
    let sigma_3_commitment_data = ProvingAssembly::<E>::commit_single_poly(&sigma_3, omegas_bitreversed, &params, &worker)?;

    transcript.commit_input(&q_l_commitment_data.oracle.get_commitment());
    transcript.commit_input(&q_r_commitment_data.oracle.get_commitment());
    transcript.commit_input(&q_o_commitment_data.oracle.get_commitment());
    transcript.commit_input(&q_m_commitment_data.oracle.get_commitment());
    transcript.commit_input(&q_c_commitment_data.oracle.get_commitment());
    transcript.commit_input(&s_id_commitment_data.oracle.get_commitment());
    transcript.commit_input(&sigma_1_commitment_data.oracle.get_commitment());
    transcript.commit_input(&sigma_2_commitment_data.oracle.get_commitment());
    transcript.commit_input(&sigma_3_commitment_data.oracle.get_commitment());

    let setup_point = transcript.get_challenge();

    let q_l_setup_value = q_l.evaluate_at(&worker, setup_point);
    let q_r_setup_value = q_r.evaluate_at(&worker, setup_point);
    let q_o_setup_value = q_o.evaluate_at(&worker, setup_point);
    let q_m_setup_value = q_m.evaluate_at(&worker, setup_point);
    let q_c_setup_value = q_c.evaluate_at(&worker, setup_point);

    let s_id_setup_value = s_id.evaluate_at(&worker, setup_point);
    let sigma_1_setup_value = sigma_1.evaluate_at(&worker, setup_point);
    let sigma_2_setup_value = sigma_2.evaluate_at(&worker, setup_point);
    let sigma_3_setup_value = sigma_3.evaluate_at(&worker, setup_point);

    let setup = RedshiftSetup::<E::Fr, FriSpecificBlake2sTree<E::Fr>> {
        n: n,
        q_l: q_l_commitment_data.oracle.get_commitment(),
        q_r: q_r_commitment_data.oracle.get_commitment(),
        q_o: q_o_commitment_data.oracle.get_commitment(),
        q_m: q_m_commitment_data.oracle.get_commitment(),
        q_c: q_c_commitment_data.oracle.get_commitment(),
        s_id: s_id_commitment_data.oracle.get_commitment(),
        sigma_1: sigma_1_commitment_data.oracle.get_commitment(),
        sigma_2: sigma_2_commitment_data.oracle.get_commitment(),
        sigma_3: sigma_3_commitment_data.oracle.get_commitment(),
    };

    let precomputation = RedshiftSetupPrecomputation::<E::Fr, FriSpecificBlake2sTree<E::Fr>> {
        q_l_aux: SinglePolySetupData::<E::Fr, FriSpecificBlake2sTree<E::Fr>> {
            poly: q_l_commitment_data.poly,
            oracle: q_l_commitment_data.oracle,
            setup_point: setup_point,
            setup_value: q_l_setup_value,
        },
        q_r_aux: SinglePolySetupData::<E::Fr, FriSpecificBlake2sTree<E::Fr>> {
            poly: q_r_commitment_data.poly,
            oracle: q_r_commitment_data.oracle,
            setup_point: setup_point,
            setup_value: q_r_setup_value,
        },
        q_o_aux: SinglePolySetupData::<E::Fr, FriSpecificBlake2sTree<E::Fr>> {
            poly: q_o_commitment_data.poly,
            oracle: q_o_commitment_data.oracle,
            setup_point: setup_point,
            setup_value: q_o_setup_value,
        },
        q_m_aux: SinglePolySetupData::<E::Fr, FriSpecificBlake2sTree<E::Fr>> {
            poly: q_m_commitment_data.poly,
            oracle: q_m_commitment_data.oracle,
            setup_point: setup_point,
            setup_value: q_m_setup_value,
        },
        q_c_aux: SinglePolySetupData::<E::Fr, FriSpecificBlake2sTree<E::Fr>> {
            poly: q_c_commitment_data.poly,
            oracle: q_c_commitment_data.oracle,
            setup_point: setup_point,
            setup_value: q_c_setup_value,
        },
        s_id_aux: SinglePolySetupData::<E::Fr, FriSpecificBlake2sTree<E::Fr>> {
            poly: s_id_commitment_data.poly,
            oracle: s_id_commitment_data.oracle,
            setup_point: setup_point,
            setup_value: s_id_setup_value,
        },
        sigma_1_aux: SinglePolySetupData::<E::Fr, FriSpecificBlake2sTree<E::Fr>> {
            poly: sigma_1_commitment_data.poly,
            oracle: sigma_1_commitment_data.oracle,
            setup_point: setup_point,
            setup_value: sigma_1_setup_value,
        },
        sigma_2_aux: SinglePolySetupData::<E::Fr, FriSpecificBlake2sTree<E::Fr>> {
            poly: sigma_2_commitment_data.poly,
            oracle: sigma_2_commitment_data.oracle,
            setup_point: setup_point,
            setup_value: sigma_2_setup_value,
        },
        sigma_3_aux: SinglePolySetupData::<E::Fr, FriSpecificBlake2sTree<E::Fr>> {
            poly: sigma_3_commitment_data.poly,
            oracle: sigma_3_commitment_data.oracle,
            setup_point: setup_point,
            setup_value: sigma_3_setup_value,
        },
    };

    Ok((setup, precomputation))
}