use crate::pairing::ff::{Field, PrimeField};
use crate::pairing::{Engine};

use crate::{SynthesisError};
use std::marker::PhantomData;

use crate::plonk::cs::gates::*;
use crate::plonk::cs::*;

use crate::multicore::*;
use crate::plonk::polynomials::*;
use crate::plonk::domains::*;
use crate::plonk::commitments::*;
use crate::plonk::utils::*;

use super::prover::ProvingAssembly;

#[derive(Debug)]
struct GeneratorAssembly<E: Engine> {
    m: usize,
    n: usize,
    input_gates: Vec<Gate<E::Fr>>,
    aux_gates: Vec<Gate<E::Fr>>,

    num_inputs: usize,
    num_aux: usize,

    inputs_map: Vec<usize>,

    is_finalized: bool,
}

impl<E: Engine> ConstraintSystem<E> for GeneratorAssembly<E> {
    const ZERO: Variable = Variable(Index::Aux(1));
    const ONE: Variable = Variable(Index::Aux(2));

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

        let gate = Gate::<E::Fr>::new_enforce_constant_gate(input_var, Some(E::Fr::zero()), self.dummy_variable());
        self.input_gates.push(gate);

        Ok(input_var)

    }

    // enforce variable as boolean
    fn enforce_boolean(&mut self, variable: Variable) -> Result<(), SynthesisError> {
        let gate = Gate::<E::Fr>::new_enforce_boolean_gate(variable, self.dummy_variable());
        self.aux_gates.push(gate);
        self.n += 1;

        Ok(())
    }

    // allocate an abstract gate
    fn new_gate<F>(&mut self, variables: (Variable, Variable, Variable), coeffs:(E::Fr, E::Fr, E::Fr, E::Fr, E::Fr), values: F) -> Result<(), SynthesisError>
    where
        F: FnOnce() -> Result<(E::Fr, E::Fr), SynthesisError>
    {
        unimplemented!()
    }

    // allocate a constant
    fn enforce_constant(&mut self, variable: Variable, constant: E::Fr) -> Result<(), SynthesisError>
    {
        let gate = Gate::<E::Fr>::new_enforce_constant_gate(variable, Some(constant), self.dummy_variable());
        self.aux_gates.push(gate);
        self.n += 1;

        Ok(())
    }

    // allocate a multiplication gate
    fn enforce_mul_2(&mut self, variables: (Variable, Variable)) -> Result<(), SynthesisError> {
        // q_l, q_r, q_o, q_c = 0, q_m = 1
        let (v_0, v_1) = variables;
        let zero = E::Fr::zero();
        let one = E::Fr::one();

        let gate = Gate::<E::Fr>::new_gate((v_0, v_1, self.dummy_variable()), (zero, zero, zero, one, zero));
        self.aux_gates.push(gate);
        self.n += 1;

        Ok(())
    }

    // allocate a multiplication gate
    fn enforce_mul_3(&mut self, variables: (Variable, Variable, Variable)) -> Result<(), SynthesisError> {
        let gate = Gate::<E::Fr>::new_multiplication_gate(variables);
        self.aux_gates.push(gate);
        self.n += 1;

        Ok(())
    }

    // allocate a linear combination gate
    fn enforce_zero_2(&mut self, variables: (Variable, Variable), coeffs:(E::Fr, E::Fr)) -> Result<(), SynthesisError>
    {
        let (v_0, v_1) = variables;
        let (c_0, c_1) = coeffs;
        let zero = E::Fr::zero();

        let gate = Gate::<E::Fr>::new_gate((v_0, v_1, self.dummy_variable()), (c_0, c_1, zero, zero, zero));
        self.aux_gates.push(gate);
        self.n += 1;

        Ok(())
    }

    // allocate a linear combination gate
    fn enforce_zero_3(&mut self, variables: (Variable, Variable, Variable), coeffs:(E::Fr, E::Fr, E::Fr)) -> Result<(), SynthesisError>
    {
        let gate = Gate::<E::Fr>::new_enforce_zero_gate(variables, coeffs);
        self.aux_gates.push(gate);
        self.n += 1;

        Ok(())
        
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

    pub(crate) fn new() -> Self {
        let mut tmp = Self {
            n: 0,
            m: 0,
            input_gates: vec![],
            aux_gates: vec![],

            num_inputs: 0,
            num_aux: 0,

            inputs_map: vec![],

            is_finalized: false,

        };

        let zero = tmp.alloc(|| Ok(E::Fr::zero())).expect("should have no issues");
        tmp.enforce_constant(zero, E::Fr::zero()).expect("should have no issues");

        let one = tmp.alloc(|| Ok(E::Fr::one())).expect("should have no issues");
        tmp.enforce_constant(one, E::Fr::one()).expect("should have no issues");

        match (zero, <Self as ConstraintSystem<E>>::ZERO) {
            (Variable(Index::Aux(1)), Variable(Index::Aux(1))) => {},
            _ => panic!("zero variable is incorrect")
        }

        match (one, <Self as ConstraintSystem<E>>::ONE) {
            (Variable(Index::Aux(2)), Variable(Index::Aux(2))) => {},
            _ => panic!("one variable is incorrect")
        }

        match (tmp.dummy_variable(), <Self as ConstraintSystem<E>>::ZERO) {
            (Variable(Index::Aux(1)), Variable(Index::Aux(1))) => {},
            _ => panic!("zero variable is incorrect")
        }

        tmp
    }

    // return variable that is not in a constraint formally, but has some value
    fn dummy_variable(&self) -> Variable {
        <Self as ConstraintSystem<E>>::ZERO
        // Variable(Index::Aux(0))
    }

    pub(crate) fn make_circuit_description_polynomials(&self, worker: &Worker) -> Result<(
        Polynomial::<E::Fr, Values>, Polynomial::<E::Fr, Values>, Polynomial::<E::Fr, Values>,
        Polynomial::<E::Fr, Values>, Polynomial::<E::Fr, Values>
    ), SynthesisError> {
        assert!(self.is_finalized);
        let total_num_gates = self.input_gates.len() + self.aux_gates.len();
        let mut q_l = vec![E::Fr::zero(); total_num_gates];
        let mut q_r = vec![E::Fr::zero(); total_num_gates];
        let mut q_o = vec![E::Fr::zero(); total_num_gates];
        let mut q_m = vec![E::Fr::zero(); total_num_gates];
        let mut q_c = vec![E::Fr::zero(); total_num_gates];

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
        for (((((gate, q_l), q_r), q_o), q_m), q_c) in self.input_gates.iter()
                                            .zip(q_l.iter_mut())
                                            .zip(q_r.iter_mut())
                                            .zip(q_o.iter_mut())
                                            .zip(q_m.iter_mut())
                                            .zip(q_c.iter_mut())
        {
            *q_l = coeff_into_field_element::<E::Fr>(&gate.q_l);
            *q_r = coeff_into_field_element::<E::Fr>(&gate.q_r);
            *q_o = coeff_into_field_element::<E::Fr>(&gate.q_o);
            *q_m = coeff_into_field_element::<E::Fr>(&gate.q_m);
            *q_c = coeff_into_field_element::<E::Fr>(&gate.q_c);
        }


        let num_input_gates = self.input_gates.len();
        let q_l_aux = &mut q_l[num_input_gates..];
        let q_r_aux = &mut q_r[num_input_gates..];
        let q_o_aux = &mut q_o[num_input_gates..];
        let q_m_aux = &mut q_m[num_input_gates..];
        let q_c_aux = &mut q_c[num_input_gates..];

        debug_assert!(self.aux_gates.len() == q_l_aux.len());

        worker.scope(self.aux_gates.len(), |scope, chunk| {
            for (((((gate, q_l), q_r), q_o), q_m), q_c) in self.aux_gates.chunks(chunk)
                                                            .zip(q_l_aux.chunks_mut(chunk))
                                                            .zip(q_r_aux.chunks_mut(chunk))
                                                            .zip(q_o_aux.chunks_mut(chunk))
                                                            .zip(q_m_aux.chunks_mut(chunk))
                                                            .zip(q_c_aux.chunks_mut(chunk))
            {
                scope.spawn(move |_| {
                    for (((((gate, q_l), q_r), q_o), q_m), q_c) in gate.iter()
                                                            .zip(q_l.iter_mut())
                                                            .zip(q_r.iter_mut())
                                                            .zip(q_o.iter_mut())
                                                            .zip(q_m.iter_mut())
                                                            .zip(q_c.iter_mut())
                        {
                            *q_l = coeff_into_field_element(&gate.q_l);
                            *q_r = coeff_into_field_element(&gate.q_r);
                            *q_o = coeff_into_field_element(&gate.q_o);
                            *q_m = coeff_into_field_element(&gate.q_m);
                            *q_c = coeff_into_field_element(&gate.q_c);
                        }
                });
            }
        });

        let q_l = Polynomial::from_values(q_l)?;
        let q_r = Polynomial::from_values(q_r)?;
        let q_o = Polynomial::from_values(q_o)?;
        let q_m = Polynomial::from_values(q_m)?;
        let q_c = Polynomial::from_values(q_c)?;

        Ok((q_l, q_r, q_o, q_m, q_c))
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

        let (q_l, q_r, q_o, q_m, q_c) = self.make_circuit_description_polynomials(&worker)?;

        let s_id = s_id.ifft(&worker);
        let sigma_1 = sigma_1.ifft(&worker);
        let sigma_2 = sigma_2.ifft(&worker);
        let sigma_3 = sigma_3.ifft(&worker);

        let q_l = q_l.ifft(&worker);
        let q_r = q_r.ifft(&worker);
        let q_o = q_o.ifft(&worker);
        let q_m = q_m.ifft(&worker);
        let q_c = q_c.ifft(&worker);

        Ok((q_l, q_r, q_o, q_m, q_c, s_id, sigma_1, sigma_2, sigma_3))
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

use super::prover::*;
use crate::plonk::fft::cooley_tukey_ntt::CTPrecomputations;

use crate::pairing::CurveAffine;

pub fn setup_with_precomputations<E: Engine, C: Circuit<E>, CP: CTPrecomputations<E::Fr>>(
    circuit: &C,
    omegas_bitreversed: &CP,
    bases: &[E::G1Affine]
    ) -> Result<(PlonkSetup<E>, PlonkSetupPrecomputation<E>), SynthesisError> 
{
    let mut assembly = GeneratorAssembly::<E>::new();
    circuit.synthesize(&mut assembly)?;
    assembly.finalize();
    
    let n = assembly.num_gates();

    let worker = Worker::new();

    let (q_l, q_r, q_o, q_m, q_c, s_id, sigma_1, sigma_2, sigma_3) = assembly.output_setup_polynomials(&worker)?;

    let q_l_commitment_data = ProvingAssembly::<E>::commit_single_poly(&q_l, &bases, &worker)?;
    let q_r_commitment_data = ProvingAssembly::<E>::commit_single_poly(&q_r, &bases, &worker)?;
    let q_o_commitment_data = ProvingAssembly::<E>::commit_single_poly(&q_o, &bases, &worker)?;
    let q_m_commitment_data = ProvingAssembly::<E>::commit_single_poly(&q_m, &bases, &worker)?;
    let q_c_commitment_data = ProvingAssembly::<E>::commit_single_poly(&q_c, &bases, &worker)?;
    let s_id_commitment_data = ProvingAssembly::<E>::commit_single_poly(&s_id, &bases, &worker)?;
    let sigma_1_commitment_data = ProvingAssembly::<E>::commit_single_poly(&sigma_1, &bases, &worker)?;
    let sigma_2_commitment_data = ProvingAssembly::<E>::commit_single_poly(&sigma_2, &bases, &worker)?;
    let sigma_3_commitment_data = ProvingAssembly::<E>::commit_single_poly(&sigma_3, &bases, &worker)?;

    let setup = PlonkSetup::<E> {
        n: n,
        q_l: q_l_commitment_data,
        q_r: q_r_commitment_data,
        q_o: q_o_commitment_data,
        q_m: q_m_commitment_data,
        q_c: q_c_commitment_data,
        s_id: s_id_commitment_data,
        sigma_1: sigma_1_commitment_data,
        sigma_2: sigma_2_commitment_data,
        sigma_3: sigma_3_commitment_data,
    };

    let coset_generator = E::Fr::multiplicative_generator();

    let q_l_lde = q_l.bitreversed_lde_using_bitreversed_ntt(&worker, 4, omegas_bitreversed, &coset_generator)?;
    let q_r_lde = q_r.bitreversed_lde_using_bitreversed_ntt(&worker, 4, omegas_bitreversed, &coset_generator)?;
    let q_o_lde = q_o.bitreversed_lde_using_bitreversed_ntt(&worker, 4, omegas_bitreversed, &coset_generator)?;
    let q_m_lde = q_m.bitreversed_lde_using_bitreversed_ntt(&worker, 4, omegas_bitreversed, &coset_generator)?;
    let q_c_lde = q_c.bitreversed_lde_using_bitreversed_ntt(&worker, 4, omegas_bitreversed, &coset_generator)?;

    let s_id_lde = s_id.bitreversed_lde_using_bitreversed_ntt(&worker, 4, omegas_bitreversed, &coset_generator)?;

    let sigma_1_lde = sigma_1.bitreversed_lde_using_bitreversed_ntt(&worker, 4, omegas_bitreversed, &coset_generator)?;
    let sigma_2_lde = sigma_2.bitreversed_lde_using_bitreversed_ntt(&worker, 4, omegas_bitreversed, &coset_generator)?;
    let sigma_3_lde = sigma_3.bitreversed_lde_using_bitreversed_ntt(&worker, 4, omegas_bitreversed, &coset_generator)?;

    let precomputation = PlonkSetupPrecomputation::<E> {
        q_l_aux: q_l_lde,
        q_r_aux: q_r_lde,
        q_o_aux: q_o_lde,
        q_m_aux: q_m_lde,
        q_c_aux: q_c_lde,
        s_id_aux: s_id_lde,
        sigma_1_aux: sigma_1_lde,
        sigma_2_aux: sigma_2_lde,
        sigma_3_aux: sigma_3_lde
    };

    Ok((setup, precomputation))
}