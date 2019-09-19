use crate::pairing::ff::{Field, PrimeField};
use crate::pairing::{Engine};

use crate::{SynthesisError};
use std::marker::PhantomData;

use crate::plonk::cs::gates::*;
use crate::plonk::cs::*;

use crate::multicore::*;
use super::polynomials::*;
use super::domains::*;

use crate::plonk::utils::*;

#[derive(Debug)]
struct GeneratorAssembly<E: Engine> {
    m: usize,
    n: usize,
    input_gates: Vec<Gate<E>>,
    aux_gates: Vec<Gate<E>>,

    num_inputs: usize,
    num_aux: usize,

    input_assingments: Vec<E::Fr>,
    aux_assingments: Vec<E::Fr>,

    inputs_map: Vec<usize>,
}

impl<E: Engine> ConstraintSystem<E> for GeneratorAssembly<E> {
    const ZERO: Variable = Variable(Index::Aux(1));
    const ONE: Variable = Variable(Index::Input(1));

    // allocate a variable
    fn alloc<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError> 
    {
        let value = value()?;

        self.num_aux += 1;
        let index = self.num_aux;
        self.aux_assingments.push(value);

        Ok(Variable(Index::Aux(index)))
    }

    // allocate an input variable
    fn alloc_input<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError> 
    {
        let value = value()?;

        self.num_inputs += 1;
        let index = self.num_inputs;
        self.input_assingments.push(value);

        let input_var = Variable(Index::Input(index));

        // let gate = Gate::<E>::new_enforce_constant_gate(input_var, Some(E::Fr::zero()), self.dummy_variable());
        let gate = Gate::<E>::new_enforce_constant_gate(input_var, Some(value), self.dummy_variable());
        self.input_gates.push(gate);

        Ok(input_var)

    }

    // enforce variable as boolean
    fn enforce_boolean(&mut self, variable: Variable) -> Result<(), SynthesisError> {
        let gate = Gate::<E>::new_enforce_boolean_gate(variable, self.dummy_variable());
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
        let gate = Gate::<E>::new_enforce_constant_gate(variable, Some(constant), self.dummy_variable());
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

        let gate = Gate::<E>::new_gate((v_0, v_1, self.dummy_variable()), (zero, zero, zero, one, zero));
        self.aux_gates.push(gate);
        self.n += 1;

        Ok(())
    }

    // allocate a multiplication gate
    fn enforce_mul_3(&mut self, variables: (Variable, Variable, Variable)) -> Result<(), SynthesisError> {
        let gate = Gate::<E>::new_multiplication_gate(variables);
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

        let gate = Gate::<E>::new_gate((v_0, v_1, self.dummy_variable()), (c_0, c_1, zero, zero, zero));
        self.aux_gates.push(gate);
        self.n += 1;

        Ok(())
    }

    // allocate a linear combination gate
    fn enforce_zero_3(&mut self, variables: (Variable, Variable, Variable), coeffs:(E::Fr, E::Fr, E::Fr)) -> Result<(), SynthesisError>
    {
        let gate = Gate::<E>::new_enforce_zero_gate(variables, coeffs);
        self.aux_gates.push(gate);
        self.n += 1;

        Ok(())
        
    }
}

impl<E: Engine> GeneratorAssembly<E> {
    fn new_empty_gate(&mut self) -> usize {
        self.n += 1;
        let index = self.n;

        self.aux_gates.push(Gate::<E>::empty());

        index
    }

    fn set_gate(&mut self, gate: Gate<E>, index: usize) {
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

            input_assingments: vec![],
            aux_assingments: vec![],

            inputs_map: vec![],

        };

        let one = tmp.alloc_input(|| Ok(E::Fr::one())).expect("should have no issues");

        let zero = tmp.alloc(|| Ok(E::Fr::zero())).expect("should have no issues");
        tmp.enforce_constant(zero, E::Fr::zero()).expect("should have no issues");

        match (one, <Self as ConstraintSystem<E>>::ONE) {
            (Variable(Index::Input(1)), Variable(Index::Input(1))) => {},
            _ => panic!("one variable is incorrect")
        }

        match (zero, <Self as ConstraintSystem<E>>::ZERO) {
            (Variable(Index::Aux(1)), Variable(Index::Aux(1))) => {},
            _ => panic!("zero variable is incorrect")
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
        // <Self as ConstraintSystem<E>>::ONE
        // Variable(Index::Aux(0))
    }

    pub(crate) fn make_wire_assingments(&self) -> (Vec<E::Fr>, Vec<E::Fr>, Vec<E::Fr>) {
        // create a vector of gate assingments
        // if a_i = j then w_j = f_l(g^i)

        let total_num_gates = self.input_gates.len() + self.aux_gates.len();
        let mut f_l = vec![E::Fr::zero(); total_num_gates];
        let mut f_r = vec![E::Fr::zero(); total_num_gates];
        let mut f_o = vec![E::Fr::zero(); total_num_gates];

        for (i, gate) in self.input_gates.iter().chain(&self.aux_gates).enumerate()
        {
            match gate.a_wire() {
                Variable(Index::Input(index)) => {
                    f_l[i] = self.input_assingments[index - 1];
                },
                Variable(Index::Aux(index)) => {
                    f_l[i] = self.aux_assingments[index - 1];
                },
            }

            match gate.b_wire() {
                Variable(Index::Input(index)) => {
                    f_r[i] = self.input_assingments[index - 1];
                },
                Variable(Index::Aux(index)) => {
                    f_r[i] = self.aux_assingments[index - 1];
                },
            }

            match gate.c_wire() {
                Variable(Index::Input(index)) => {
                    f_o[i] = self.input_assingments[index - 1];
                },
                Variable(Index::Aux(index)) => {
                    f_o[i] = self.aux_assingments[index - 1];
                },
            }
        }

        (f_l, f_r, f_o)
    }

    pub(crate) fn make_circuit_description_polynomials(&self, worker: &Worker) -> Result<(
        Polynomial::<E::Fr, Values>, Polynomial::<E::Fr, Values>, Polynomial::<E::Fr, Values>,
        Polynomial::<E::Fr, Values>, Polynomial::<E::Fr, Values>
    ), SynthesisError> {
        let total_num_gates = self.input_gates.len() + self.aux_gates.len();
        let mut q_l = vec![E::Fr::zero(); total_num_gates];
        let mut q_r = vec![E::Fr::zero(); total_num_gates];
        let mut q_o = vec![E::Fr::zero(); total_num_gates];
        let mut q_m = vec![E::Fr::zero(); total_num_gates];
        let mut q_c = vec![E::Fr::zero(); total_num_gates];

        fn coeff_into_field_element<E: Engine>(coeff: & Coeff<E>) -> E::Fr {
            match coeff {
                Coeff::Zero => {
                    E::Fr::zero()
                },
                Coeff::One => {
                    E::Fr::one()
                },
                Coeff::NegativeOne => {
                    let mut tmp = E::Fr::one();
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
            *q_l = coeff_into_field_element(&gate.q_l);
            *q_r = coeff_into_field_element(&gate.q_r);
            *q_o = coeff_into_field_element(&gate.q_o);
            *q_m = coeff_into_field_element(&gate.q_m);
            *q_c = coeff_into_field_element(&gate.q_c);
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

    // no ZK for now
    pub(crate) fn generate_proof(&self) -> Result<(), SynthesisError> {
        let n = self.input_gates.len() + self.aux_gates.len();

        // we need n+1 to be a power of two and can not have n to be power of two
        let required_domain_size = n + 1;
        assert!(required_domain_size.is_power_of_two());

        let worker = Worker::new();

        let (w_l, w_r, w_o) = self.make_wire_assingments();

        let w_l = Polynomial::<E::Fr, Values>::from_values_unpadded(w_l)?;
        let w_r = Polynomial::<E::Fr, Values>::from_values_unpadded(w_r)?;
        let w_o = Polynomial::<E::Fr, Values>::from_values_unpadded(w_o)?;

        let a_poly = w_l.clone_padded_to_domain()?.ifft(&worker);
        let b_poly = w_r.clone_padded_to_domain()?.ifft(&worker);
        let c_poly = w_o.clone_padded_to_domain()?.ifft(&worker);

        let beta = E::Fr::from_str("15").unwrap();
        let gamma = E::Fr::from_str("4").unwrap();

        let mut w_l_plus_gamma = w_l.clone();
        w_l_plus_gamma.add_constant(&worker, &gamma);

        let mut w_r_plus_gamma = w_r.clone();
        w_r_plus_gamma.add_constant(&worker, &gamma);

        let mut w_o_plus_gamma = w_o.clone();
        w_o_plus_gamma.add_constant(&worker, &gamma);

        let z_1 = {
            let n = self.input_gates.len() + self.aux_gates.len();
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
            let (sigma_1, sigma_2, sigma_3) = self.calculate_permutations_as_in_a_paper();

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

        let mut z_1_shifted = z_1.clone();
        z_1_shifted.distribute_powers(&worker, z_1.omega);
        
        let mut z_2_shifted = z_2.clone();
        z_2_shifted.distribute_powers(&worker, z_2.omega);
        
        let a_lde = a_poly.clone().coset_lde(&worker, 4)?;
        let b_lde = b_poly.clone().coset_lde(&worker, 4)?;
        let c_lde = c_poly.clone().coset_lde(&worker, 4)?;

        let (q_l, q_r, q_o, q_m, q_c, s_id, sigma_1, sigma_2, sigma_3) = self.output_setup_polynomials(&worker)?;

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

        let alpha = E::Fr::from_str("3").unwrap();

        let mut vanishing_poly_inverse = self.calculate_inverse_vanishing_polynomial_in_a_coset(&worker, q_c_lde.size(), required_domain_size.next_power_of_two())?;

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

        let l_0 = self.calculate_lagrange_poly(&worker, required_domain_size.next_power_of_two(), 0)?;
        let l_n_minus_one = self.calculate_lagrange_poly(&worker, required_domain_size.next_power_of_two(), n-1)?;

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

        let z = E::Fr::from_str("123").unwrap();

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

        let mut inverse_vanishing_at_z = self.evaluate_inverse_vanishing_poly(required_domain_size.next_power_of_two(), z);

        let inverse_vanishing_at_z_no_alphas = inverse_vanishing_at_z;

        let z_1_at_z = z_1.evaluate_at(&worker, z);
        let z_2_at_z = z_2.evaluate_at(&worker, z);

        let z_1_shifted_at_z = z_1_shifted.evaluate_at(&worker, z);
        let z_2_shifted_at_z = z_2_shifted.evaluate_at(&worker, z);

        let l_0_at_z = l_0.evaluate_at(&worker, z);
        let l_n_minus_one_at_z = l_n_minus_one.evaluate_at(&worker, z);

        let t_at_z = t_poly.evaluate_at(&worker, z);

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

        let r_at_z = r_1.evaluate_at(&worker, z);

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

        Ok(())
    }

    fn finalize(&mut self) {
        let n = self.input_gates.len() + self.aux_gates.len();
        if (n+1).is_power_of_two() {
            return;
        }

        let empty_gate = Gate::<E>::new_empty_gate(self.dummy_variable());

        let new_aux_len = (n+1).next_power_of_two() - 1 - self.input_gates.len();

        self.aux_gates.resize(new_aux_len, empty_gate);
    }

    fn calculate_inverse_vanishing_polynomial_in_a_coset(&self, worker: &Worker, poly_size:usize, vahisning_size: usize) -> Result<Polynomial::<E::Fr, Values>, SynthesisError> {
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

    fn evaluate_inverse_vanishing_poly(&self, vahisning_size: usize, point: E::Fr) -> E::Fr {
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

    fn calculate_lagrange_poly(&self, worker: &Worker, poly_size:usize, poly_number: usize) -> Result<Polynomial::<E::Fr, Coefficients>, SynthesisError> {
        assert!(poly_size.is_power_of_two());
        assert!(poly_number < poly_size);

        let mut poly = Polynomial::<E::Fr, Values>::from_values(vec![E::Fr::zero(); poly_size])?;

        poly.as_mut()[poly_number] = E::Fr::one();

        Ok(poly.ifft(&worker))
    }
}




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

        // println!("L = {:?}", f_l);
        // println!("R = {:?}", f_r);
        // println!("O = {:?}", f_o);

        let (sigma_1, sigma_2, sigma_3) = assembly.calculate_permutations_as_in_a_paper();
        // println!("Sigma 1 = {:?}", sigma_1);
        // println!("Sigma 2 = {:?}", sigma_2);
        // println!("Sigma 3 = {:?}", sigma_3);

        let num_gates = assembly.num_gates();

        let mut id_1: Vec<_> = (1..=num_gates).collect();
        let mut id_2: Vec<_> = ((num_gates+1)..=(2*num_gates)).collect();
        let mut id_3: Vec<_> = ((2*num_gates + 1)..=(3*num_gates)).collect();

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

        // println!("F = {:?}", f_prime);
        // println!("G = {:?}", g_prime);

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