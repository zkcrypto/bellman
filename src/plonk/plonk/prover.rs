use crate::pairing::ff::{Field, PrimeField};
use crate::pairing::{Engine};
use crate::plonk::transparent_engine::TransparentEngine;

use crate::{SynthesisError};
use std::marker::PhantomData;

use crate::plonk::cs::gates::*;
use crate::plonk::cs::*;

use crate::multicore::*;
use crate::plonk::domains::*;
use crate::plonk::commitments::*;
use crate::plonk::commitments::transcript::*;
use crate::plonk::utils::*;
use crate::plonk::polynomials::*;

#[derive(Debug, Clone)]
pub struct ProvingAssembly<E: Engine> {
    m: usize,
    n: usize,
    input_gates: Vec<Gate<E::Fr>>,
    aux_gates: Vec<Gate<E::Fr>>,

    num_inputs: usize,
    num_aux: usize,

    input_assingments: Vec<E::Fr>,
    aux_assingments: Vec<E::Fr>,

    inputs_map: Vec<usize>,

    is_finalized: bool
}

impl<E: Engine> ConstraintSystem<E> for ProvingAssembly<E> {
    // const ZERO: Variable = Variable(Index::Aux(1));
    // const ONE: Variable = Variable(Index::Aux(2));

    // allocate a variable
    fn alloc<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError> 
    {
        let value = value()?;

        self.num_aux += 1;
        let index = self.num_aux;
        self.aux_assingments.push(value);

        // println!("Allocated variable Aux({}) with value {}", index, value);

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

        let gate = Gate::<E::Fr>::new_enforce_constant_gate(input_var, Some(E::Fr::zero()), self.dummy_variable());
        // let gate = Gate::<E>::new_enforce_constant_gate(input_var, Some(value), self.dummy_variable());
        self.input_gates.push(gate);

        // println!("Allocated input Input({}) with value {}", index, value);

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
    fn new_gate(&mut self, variables: (Variable, Variable, Variable), 
        coeffs:(E::Fr,E::Fr,E::Fr,E::Fr,E::Fr)) -> Result<(), SynthesisError>
    {
        let gate = Gate::<E::Fr>::new_gate(variables, coeffs);
        // println!("Enforced new gate number {}: {:?}", self.n, gate);
        self.aux_gates.push(gate);
        self.n += 1;

        // let satisfied = self.clone().is_satisfied();
        // if !satisfied {
        //     return Err(SynthesisError::Unsatisfiable);
        // }

        Ok(())
    }

    // allocate a constant
    fn enforce_constant(&mut self, variable: Variable, constant: E::Fr) -> Result<(), SynthesisError>
    {
        let gate = Gate::<E::Fr>::new_enforce_constant_gate(variable, Some(constant), self.dummy_variable());
        // println!("Enforced new constant gate number {}: {:?}", self.n, gate);
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

    fn get_value(&self, var: Variable) -> Result<E::Fr, SynthesisError> {
        let value = match var {
            Variable(Index::Input(input)) => {
                self.input_assingments[input - 1]
            },
            Variable(Index::Aux(aux)) => {
                self.aux_assingments[aux - 1]
            }
        };

        Ok(value)
    }

    fn get_dummy_variable(&self) -> Variable {
        self.dummy_variable()
    }
}

impl<E: Engine> ProvingAssembly<E> {
    pub fn new() -> Self {
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

            is_finalized: false,
        };

        let zero = tmp.alloc(|| Ok(E::Fr::zero())).expect("should have no issues");
        tmp.enforce_constant(zero, E::Fr::zero()).expect("should have no issues");

        // let one = tmp.alloc(|| Ok(E::Fr::one())).expect("should have no issues");
        // tmp.enforce_constant(one, E::Fr::one()).expect("should have no issues");

        // match (zero, <Self as ConstraintSystem<E>>::ZERO) {
        //     (Variable(Index::Aux(1)), Variable(Index::Aux(1))) => {},
        //     _ => panic!("zero variable is incorrect")
        // }

        // match (one, <Self as ConstraintSystem<E>>::ONE) {
        //     (Variable(Index::Aux(2)), Variable(Index::Aux(2))) => {},
        //     _ => panic!("one variable is incorrect")
        // }

        match (tmp.dummy_variable(), zero) {
            (Variable(Index::Aux(1)), Variable(Index::Aux(1))) => {},
            _ => panic!("zero variable is incorrect")
        }

        tmp
    }

    fn new_empty_gate(&mut self) -> usize {
        self.n += 1;
        let index = self.n;

        self.aux_gates.push(Gate::<E::Fr>::empty());

        index
    }

    fn set_gate(&mut self, gate: Gate<E::Fr>, index: usize) {
        self.aux_gates[index-1] = gate;
    }

    // return variable that is not in a constraint formally, but has some value
    fn dummy_variable(&self) -> Variable {
        // <Self as ConstraintSystem<E>>::ZERO
        Variable(Index::Aux(1))
    }

    pub(crate) fn make_wire_assingments(&self) -> (Vec<E::Fr>, Vec<E::Fr>, Vec<E::Fr>) {
        assert!(self.is_finalized);
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
        assert!(self.is_finalized);

        let total_num_gates = self.input_gates.len() + self.aux_gates.len();
        let mut q_l = vec![E::Fr::zero(); total_num_gates];
        let mut q_r = vec![E::Fr::zero(); total_num_gates];
        let mut q_o = vec![E::Fr::zero(); total_num_gates];
        let mut q_m = vec![E::Fr::zero(); total_num_gates];
        let mut q_c = vec![E::Fr::zero(); total_num_gates];

        fn coeff_into_field_element<F: PrimeField>(coeff: & Coeff<F>) -> F {
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

    pub fn num_gates(&self) -> usize {
        assert!(self.is_finalized);

        self.input_gates.len() + self.aux_gates.len()
    }

    pub fn finalize(&mut self) {
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

        self.is_finalized = true;
    }

    pub fn is_satisfied(mut self) -> bool {
        // self.finalize();
        // assert!(self.is_finalized);

        fn coeff_into_field_element<F: PrimeField>(coeff: & Coeff<F>) -> F {
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
        for (i, gate) in self.input_gates.iter().enumerate()
        {
            let q_l = coeff_into_field_element(&gate.q_l);
            let q_r = coeff_into_field_element(&gate.q_r);
            let q_o = coeff_into_field_element(&gate.q_o);
            let q_m = coeff_into_field_element(&gate.q_m);
            let q_c = coeff_into_field_element(&gate.q_c);

            assert!(q_c.is_zero(), "should not hardcode a constant into the input gate");

            let a_value = self.get_value(*gate.a_wire()).expect("must get a variable value");
            let b_value = self.get_value(*gate.b_wire()).expect("must get a variable value");
            let c_value = self.get_value(*gate.c_wire()).expect("must get a variable value");

            let input_value = self.input_assingments[i];
            let mut res = input_value;
            res.negate();

            let mut tmp = q_l;
            tmp.mul_assign(&a_value);
            res.add_assign(&tmp);

            let mut tmp = q_r;
            tmp.mul_assign(&b_value);
            res.add_assign(&tmp);

            let mut tmp = q_o;
            tmp.mul_assign(&c_value);
            res.add_assign(&tmp);

            let mut tmp = q_m;
            tmp.mul_assign(&a_value);
            tmp.mul_assign(&b_value);
            res.add_assign(&tmp);

            if !res.is_zero() {
                println!("Unsatisfied at input gate {}: {:?}", i+1, gate);
                println!("A value = {}, B value = {}, C value = {}", a_value, b_value, c_value);
                return false;
            }
        }

        for (i, gate) in self.aux_gates.iter().enumerate()
        {
            let q_l = coeff_into_field_element(&gate.q_l);
            let q_r = coeff_into_field_element(&gate.q_r);
            let q_o = coeff_into_field_element(&gate.q_o);
            let q_m = coeff_into_field_element(&gate.q_m);
            let q_c = coeff_into_field_element(&gate.q_c);

            let a_value = self.get_value(*gate.a_wire()).expect("must get a variable value");
            let b_value = self.get_value(*gate.b_wire()).expect("must get a variable value");
            let c_value = self.get_value(*gate.c_wire()).expect("must get a variable value");

            let mut res = q_c;

            let mut tmp = q_l;
            tmp.mul_assign(&a_value);
            res.add_assign(&tmp);

            let mut tmp = q_r;
            tmp.mul_assign(&b_value);
            res.add_assign(&tmp);

            let mut tmp = q_o;
            tmp.mul_assign(&c_value);
            res.add_assign(&tmp);

            let mut tmp = q_m;
            tmp.mul_assign(&a_value);
            tmp.mul_assign(&b_value);
            res.add_assign(&tmp);

            if !res.is_zero() {
                println!("Unsatisfied at aux gate {}", i+1);
                println!("Gate {:?}", *gate);
                println!("A = {}, B = {}, C = {}", a_value, b_value, c_value);
                return false;
            }
        }

        true
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

// pub struct RedshiftProof<F: PrimeField, I: IopInstance<F>, FRI: FriIop<F, IopType = I>>{
//     pub a_opening_value: F,
//     pub b_opening_value: F,
//     pub c_opening_value: F,
//     pub q_l_opening_value: F,
//     pub q_r_opening_value: F,
//     pub q_o_opening_value: F,
//     pub q_m_opening_value: F,
//     pub q_c_opening_value: F,
//     pub s_id_opening_value: F,
//     pub sigma_1_opening_value: F,
//     pub sigma_2_opening_value: F,
//     pub sigma_3_opening_value: F,
//     pub z_1_unshifted_opening_value: F,
//     pub z_2_unshifted_opening_value: F,
//     pub z_1_shifted_opening_value: F,
//     pub z_2_shifted_opening_value: F,
//     pub t_low_opening_value: F,
//     pub t_mid_opening_value: F,
//     pub t_high_opening_value: F,
//     pub a_commitment: I::Commitment,
//     pub b_commitment: I::Commitment,
//     pub c_commitment: I::Commitment,
//     pub z_1_commitment: I::Commitment,
//     pub z_2_commitment: I::Commitment,
//     pub t_low_commitment: I::Commitment,
//     pub t_mid_commitment: I::Commitment,
//     pub t_high_commitment: I::Commitment,
//     pub openings_proof: FRI::Proof,
// }

use crate::plonk::fft::cooley_tukey_ntt::CTPrecomputations;

use crate::pairing::{CurveAffine, CurveProjective};
use crate::pairing::EncodedPoint;

#[derive(Debug)]
pub struct PlonkSetup<E: Engine>{
    pub n: usize,
    pub q_l: E::G1Affine,
    pub q_r: E::G1Affine,
    pub q_o: E::G1Affine,
    pub q_m: E::G1Affine,
    pub q_c: E::G1Affine,
    pub s_id: E::G1Affine,
    pub sigma_1: E::G1Affine,
    pub sigma_2: E::G1Affine,
    pub sigma_3: E::G1Affine,
}

// #[derive(Debug)]
pub struct PlonkSetupPrecomputation<E: Engine>{
    pub q_l_aux: Polynomial<E::Fr, Values>,
    pub q_r_aux: Polynomial<E::Fr, Values>,
    pub q_o_aux: Polynomial<E::Fr, Values>,
    pub q_m_aux: Polynomial<E::Fr, Values>,
    pub q_c_aux: Polynomial<E::Fr, Values>,
    pub s_id_aux: Polynomial<E::Fr, Values>,
    pub sigma_1_aux: Polynomial<E::Fr, Values>,
    pub sigma_2_aux: Polynomial<E::Fr, Values>,
    pub sigma_3_aux: Polynomial<E::Fr, Values>,
}

struct OpeningRequest<'a, E: Engine> {
    polynomials: Vec<&'a Polynomial<E::Fr, Coefficients>>,
    opening_point: E::Fr,
    opening_values: Vec<E::Fr>
}

use crate::multiexp::dense_multiexp;

pub(crate) fn field_elements_into_representations<E: Engine>(
    worker: &Worker,
    scalars: Vec<E::Fr>
) -> Result<Vec<<E::Fr as PrimeField>::Repr>, SynthesisError>
{   
    let mut representations = vec![<E::Fr as PrimeField>::Repr::default(); scalars.len()];
    worker.scope(scalars.len(), |scope, chunk| {
        for (scalar, repr) in scalars.chunks(chunk)
                    .zip(representations.chunks_mut(chunk)) {
            scope.spawn(move |_| {
                for (scalar, repr) in scalar.iter()
                                        .zip(repr.iter_mut()) {
                    *repr = scalar.into_repr();
                }
            });
        }
    });

    Ok(representations)
}

impl<E: Engine> ProvingAssembly<E> {
    pub(crate) fn commit_single_poly(
        poly: &Polynomial<E::Fr, Coefficients>, 
        bases: &[E::G1Affine],
        worker: &Worker
    ) -> Result<E::G1Affine, SynthesisError> {
        let reprs = field_elements_into_representations::<E>(&worker, poly.as_ref().to_owned())?;
        let result = dense_multiexp(&worker, bases, &reprs)?;

        Ok(result.into_affine())
    }

    fn divide_single(
        poly: &[E::Fr],
        opening_point: E::Fr,
    ) -> Vec<E::Fr> {
        // we are only interested in quotient without a reminder, so we actually don't need opening value
        let mut b = opening_point;
        b.negate();

        let mut q = vec![E::Fr::zero(); poly.len()];

        let mut tmp = E::Fr::zero();
        let mut found_one = false;
        for (q, r) in q.iter_mut().rev().skip(1).zip(poly.iter().rev()) {
            if !found_one {
                if r.is_zero() {
                    continue
                } else {
                    found_one = true;
                }
            }

            let mut lead_coeff = *r;
            lead_coeff.sub_assign(&tmp);
            *q = lead_coeff;
            tmp = lead_coeff;
            tmp.mul_assign(&b);
        }

        q
    }

    fn multiopening<T: Transcript<E::Fr>>
        ( 
            opening_request: OpeningRequest<E>,
            bases: &[E::G1Affine],
            worker: &Worker,
            transcript: &mut T
        ) -> Result<E::G1Affine, SynthesisError> {
            let required_size = opening_request.polynomials[0].size();

            let mut final_aggregate = Polynomial::from_coeffs(vec![E::Fr::zero(); required_size])?;

            let aggregation_challenge = transcript.get_challenge();

            let mut alpha = E::Fr::one();

            for poly in opening_request.polynomials.iter() {
                final_aggregate.add_assign_scaled(&worker, poly, &alpha);

                alpha.mul_assign(&aggregation_challenge);
            }

            let q = Self::divide_single(final_aggregate.as_ref(), opening_request.opening_point);

            let q = Polynomial::from_coeffs(q)?;

            let opening = Self::commit_single_poly(&q, bases, &worker)?;

            Ok(opening)
    }

    fn prove_with_setup_precomputed<CP: CTPrecomputations<E::Fr>, CPI: CTPrecomputations<E::Fr>, T: Transcript<E::Fr> >(
        self,
        setup_precomp: &PlonkSetupPrecomputation<E>,
        worker: &Worker,
        omegas_bitreversed: &CP,
        omegas_inv_bitreversed: &CPI,
        bases: &[E::G1Affine]
    ) -> Result<(), SynthesisError> {
        assert!(self.is_finalized);

        let mut transcript = T::new();

        let n = self.input_gates.len() + self.aux_gates.len();

        // we need n+1 to be a power of two and can not have n to be power of two
        let required_domain_size = n + 1;
        assert!(required_domain_size.is_power_of_two());

        let (w_l, w_r, w_o) = self.make_wire_assingments();

        // these are 2^k - 1 size and explicitly unpadded
        let w_l = Polynomial::<E::Fr, Values>::from_values_unpadded(w_l)?;
        let w_r = Polynomial::<E::Fr, Values>::from_values_unpadded(w_r)?;
        let w_o = Polynomial::<E::Fr, Values>::from_values_unpadded(w_o)?;

        let a_poly = w_l.clone_padded_to_domain()?.ifft_using_bitreversed_ntt(&worker, omegas_inv_bitreversed, &E::Fr::one())?;
        let b_poly = w_r.clone_padded_to_domain()?.ifft_using_bitreversed_ntt(&worker, omegas_inv_bitreversed, &E::Fr::one())?;
        let c_poly = w_o.clone_padded_to_domain()?.ifft_using_bitreversed_ntt(&worker, omegas_inv_bitreversed, &E::Fr::one())?;

        // polynomials inside of these is are values in cosets

        let a_commitment_data = Self::commit_single_poly(&a_poly, bases, &worker)?;
        let b_commitment_data = Self::commit_single_poly(&b_poly, bases, &worker)?;
        let c_commitment_data = Self::commit_single_poly(&c_poly, bases, &worker)?;

        transcript.commit_bytes(a_commitment_data.into_compressed().as_ref());
        transcript.commit_bytes(b_commitment_data.into_compressed().as_ref());
        transcript.commit_bytes(c_commitment_data.into_compressed().as_ref());

        // TODO: Add public inputs

        let beta = transcript.get_challenge();
        let gamma = transcript.get_challenge();

        let mut w_l_plus_gamma = w_l.clone();
        w_l_plus_gamma.add_constant(&worker, &gamma);

        let mut w_r_plus_gamma = w_r.clone();
        w_r_plus_gamma.add_constant(&worker, &gamma);

        let mut w_o_plus_gamma = w_o.clone();
        w_o_plus_gamma.add_constant(&worker, &gamma);

        // we take A, B, C values and form (A + beta*i + gamma), etc and calculate their grand product

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

            drop(w_l_contribution);

            let values = grand_product.into_coeffs();
            assert!((values.len() + 1).is_power_of_two());
            let mut prepadded = Vec::with_capacity(values.len() + 1);
            prepadded.push(E::Fr::one());
            prepadded.extend(values);

            let z_2 = Polynomial::<E::Fr, Values>::from_values(prepadded)?;

            z_2
        };

        assert!(z_2.as_ref().last().expect("must exist") == z_1.as_ref().last().expect("must exist"));

        // interpolate on the main domain
        let z_1 = z_1.ifft_using_bitreversed_ntt(&worker, omegas_inv_bitreversed, &E::Fr::one())?;
        let z_2 = z_2.ifft_using_bitreversed_ntt(&worker, omegas_inv_bitreversed, &E::Fr::one())?;

        // polynomials inside of these is are values in cosets

        let z_1_commitment_data = Self::commit_single_poly(&z_1, &bases, &worker)?;
        let z_2_commitment_data = Self::commit_single_poly(&z_2, &bases, &worker)?;

        transcript.commit_bytes(z_1_commitment_data.into_compressed().as_ref());
        transcript.commit_bytes(z_2_commitment_data.into_compressed().as_ref());

        let mut z_1_shifted = z_1.clone();
        z_1_shifted.distribute_powers(&worker, z_1.omega);
        
        let mut z_2_shifted = z_2.clone();
        z_2_shifted.distribute_powers(&worker, z_2.omega);


        let a_coset_lde_bitreversed = a_poly.clone().bitreversed_lde_using_bitreversed_ntt(
            &worker, 
            4, 
            omegas_bitreversed, 
            &E::Fr::multiplicative_generator()
        )?;

        let b_coset_lde_bitreversed = b_poly.clone().bitreversed_lde_using_bitreversed_ntt(
            &worker, 
            4, 
            omegas_bitreversed, 
            &E::Fr::multiplicative_generator()
        )?;

        let c_coset_lde_bitreversed = c_poly.clone().bitreversed_lde_using_bitreversed_ntt(
            &worker, 
            4, 
            omegas_bitreversed, 
            &E::Fr::multiplicative_generator()
        )?;
        
        let q_l_coset_lde_bitreversed = setup_precomp.q_l_aux.clone();
        let q_r_coset_lde_bitreversed = setup_precomp.q_r_aux.clone();
        let q_o_coset_lde_bitreversed = setup_precomp.q_o_aux.clone();
        let q_m_coset_lde_bitreversed = setup_precomp.q_m_aux.clone();
        let q_c_coset_lde_bitreversed = setup_precomp.q_c_aux.clone();
        let s_id_coset_lde_bitreversed = setup_precomp.s_id_aux.clone();
        let sigma_1_coset_lde_bitreversed = setup_precomp.sigma_1_aux.clone();
        let sigma_2_coset_lde_bitreversed = setup_precomp.sigma_2_aux.clone();
        let sigma_3_coset_lde_bitreversed = setup_precomp.sigma_3_aux.clone();

        let (q_l, q_r, q_o, q_m, q_c, s_id, sigma_1, sigma_2, sigma_3) = self.output_setup_polynomials(&worker)?;

        // we do not commit those cause those are known already

        let n_fe = E::Fr::from_str(&n.to_string()).expect("must be valid field element");
        let mut two_n_fe = n_fe;
        two_n_fe.double();

        let alpha = transcript.get_challenge();

        // TODO: may be speedup this one too
        let mut vanishing_poly_inverse_bitreversed = self.calculate_inverse_vanishing_polynomial_in_a_coset(&worker, q_l_coset_lde_bitreversed.size(), required_domain_size.next_power_of_two())?;
        vanishing_poly_inverse_bitreversed.bitreverse_enumeration(&worker);

        let mut t_1 = {
            let mut t_1 = q_c_coset_lde_bitreversed;

            let mut q_l_by_a = q_l_coset_lde_bitreversed;
            q_l_by_a.mul_assign(&worker, &a_coset_lde_bitreversed);
            t_1.add_assign(&worker, &q_l_by_a);
            drop(q_l_by_a);

            let mut q_r_by_b = q_r_coset_lde_bitreversed;
            q_r_by_b.mul_assign(&worker, &b_coset_lde_bitreversed);
            t_1.add_assign(&worker, &q_r_by_b);
            drop(q_r_by_b);

            let mut q_o_by_c = q_o_coset_lde_bitreversed;
            q_o_by_c.mul_assign(&worker, &c_coset_lde_bitreversed);
            t_1.add_assign(&worker, &q_o_by_c);
            drop(q_o_by_c);

            let mut q_m_by_ab = q_m_coset_lde_bitreversed;
            q_m_by_ab.mul_assign(&worker, &a_coset_lde_bitreversed);
            q_m_by_ab.mul_assign(&worker, &b_coset_lde_bitreversed);
            t_1.add_assign(&worker, &q_m_by_ab);
            drop(q_m_by_ab);

            vanishing_poly_inverse_bitreversed.scale(&worker, alpha);

            t_1.mul_assign(&worker, &vanishing_poly_inverse_bitreversed);

            t_1
        };

        fn get_degree<F: PrimeField>(poly: &Polynomial<F, Coefficients>) -> usize {
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

        let z_1_coset_lde_bitreversed = z_1.clone().bitreversed_lde_using_bitreversed_ntt(
            &worker, 
            4, 
            omegas_bitreversed, 
            &E::Fr::multiplicative_generator()
        )?;

        assert!(z_1_coset_lde_bitreversed.size() == required_domain_size*4);

        let z_1_shifted_coset_lde_bitreversed = z_1_shifted.clone().bitreversed_lde_using_bitreversed_ntt(
            &worker, 
            4, 
            omegas_bitreversed, 
            &E::Fr::multiplicative_generator()
        )?;

        assert!(z_1_shifted_coset_lde_bitreversed.size() == required_domain_size*4);

        let z_2_coset_lde_bitreversed = z_2.clone().bitreversed_lde_using_bitreversed_ntt(
            &worker, 
            4, 
            omegas_bitreversed, 
            &E::Fr::multiplicative_generator()
        )?;

        assert!(z_2_coset_lde_bitreversed.size() == required_domain_size*4);

        let z_2_shifted_coset_lde_bitreversed = z_2_shifted.clone().bitreversed_lde_using_bitreversed_ntt(
            &worker, 
            4, 
            omegas_bitreversed, 
            &E::Fr::multiplicative_generator()
        )?;

        assert!(z_2_shifted_coset_lde_bitreversed.size() == required_domain_size*4);

        // (A + beta*i + gamma)(B + beta(n+i) + gamma)(C + beta(2n+i) + gamma)*Z(k) = Z(k+1)
        {
            // TODO: May be optimize number of additions
            let mut contrib_z_1 = z_1_coset_lde_bitreversed.clone();

            let mut s_id_by_beta = s_id_coset_lde_bitreversed;
            s_id_by_beta.scale(&worker, beta);

            let mut n_by_beta = n_fe;
            n_by_beta.mul_assign(&beta);

            let mut a_perm = s_id_by_beta.clone();
            a_perm.add_constant(&worker, &gamma);
            a_perm.add_assign(&worker, &a_coset_lde_bitreversed);
            contrib_z_1.mul_assign(&worker, &a_perm);
            drop(a_perm);

            s_id_by_beta.add_constant(&worker, &n_by_beta);

            let mut b_perm = s_id_by_beta.clone();

            b_perm.add_constant(&worker, &gamma);
            b_perm.add_assign(&worker, &b_coset_lde_bitreversed);
            contrib_z_1.mul_assign(&worker, &b_perm);
            drop(b_perm);

            s_id_by_beta.add_constant(&worker, &n_by_beta);

            let mut c_perm = s_id_by_beta;
            c_perm.add_constant(&worker, &gamma);
            c_perm.add_assign(&worker, &c_coset_lde_bitreversed);
            contrib_z_1.mul_assign(&worker, &c_perm);
            drop(c_perm);

            contrib_z_1.sub_assign(&worker, &z_1_shifted_coset_lde_bitreversed);

            vanishing_poly_inverse_bitreversed.scale(&worker, alpha);

            contrib_z_1.mul_assign(&worker, &vanishing_poly_inverse_bitreversed);

            t_1.add_assign(&worker, &contrib_z_1);
        }

        {
            // TODO: May be optimize number of additions
            let mut contrib_z_2 = z_2_coset_lde_bitreversed.clone();

            let mut a_perm = sigma_1_coset_lde_bitreversed;
            a_perm.scale(&worker, beta);
            a_perm.add_constant(&worker, &gamma);
            a_perm.add_assign(&worker, &a_coset_lde_bitreversed);
            contrib_z_2.mul_assign(&worker, &a_perm);
            drop(a_perm);


            let mut b_perm = sigma_2_coset_lde_bitreversed;
            b_perm.scale(&worker, beta);
            b_perm.add_constant(&worker, &gamma);
            b_perm.add_assign(&worker, &b_coset_lde_bitreversed);
            contrib_z_2.mul_assign(&worker, &b_perm);
            drop(b_perm);

            let mut c_perm = sigma_3_coset_lde_bitreversed;
            c_perm.scale(&worker, beta);
            c_perm.add_constant(&worker, &gamma);
            c_perm.add_assign(&worker, &c_coset_lde_bitreversed);
            contrib_z_2.mul_assign(&worker, &c_perm);
            drop(c_perm);

            contrib_z_2.sub_assign(&worker, &z_2_shifted_coset_lde_bitreversed);

            vanishing_poly_inverse_bitreversed.scale(&worker, alpha);

            contrib_z_2.mul_assign(&worker, &vanishing_poly_inverse_bitreversed);

            t_1.add_assign(&worker, &contrib_z_2);
        }

        drop(a_coset_lde_bitreversed);
        drop(b_coset_lde_bitreversed);
        drop(c_coset_lde_bitreversed);

        let l_0 = self.calculate_lagrange_poly(&worker, required_domain_size.next_power_of_two(), 0)?;
        let l_n_minus_one = self.calculate_lagrange_poly(&worker, required_domain_size.next_power_of_two(), n-1)?;

        {
            let mut z_1_minus_z_2_shifted = z_1_shifted_coset_lde_bitreversed.clone();
            z_1_minus_z_2_shifted.sub_assign(&worker, &z_2_shifted_coset_lde_bitreversed);

            let l_coset_lde_bitreversed = l_n_minus_one.clone().bitreversed_lde_using_bitreversed_ntt(
                &worker, 
                4, 
                omegas_bitreversed, 
                &E::Fr::multiplicative_generator()
            )?;

            z_1_minus_z_2_shifted.mul_assign(&worker, &l_coset_lde_bitreversed);
            drop(l_coset_lde_bitreversed);

            vanishing_poly_inverse_bitreversed.scale(&worker, alpha);

            z_1_minus_z_2_shifted.mul_assign(&worker, &vanishing_poly_inverse_bitreversed);

            t_1.add_assign(&worker, &z_1_minus_z_2_shifted);
        }

        {
            let mut z_1_minus_z_2 = z_1_coset_lde_bitreversed.clone();
            z_1_minus_z_2.sub_assign(&worker, &z_2_coset_lde_bitreversed);

            let l_coset_lde_bitreversed = l_0.clone().bitreversed_lde_using_bitreversed_ntt(
                &worker, 
                4, 
                omegas_bitreversed, 
                &E::Fr::multiplicative_generator()
            )?;

            z_1_minus_z_2.mul_assign(&worker, &l_coset_lde_bitreversed);
            drop(l_coset_lde_bitreversed);

            vanishing_poly_inverse_bitreversed.scale(&worker, alpha);

            z_1_minus_z_2.mul_assign(&worker, &vanishing_poly_inverse_bitreversed);

            t_1.add_assign(&worker, &z_1_minus_z_2);
        }

        drop(z_1_coset_lde_bitreversed);
        drop(z_2_coset_lde_bitreversed);
        drop(z_1_shifted_coset_lde_bitreversed);
        drop(z_2_shifted_coset_lde_bitreversed);

        t_1.bitreverse_enumeration(&worker);

        let t_poly = t_1.icoset_fft_for_generator(&worker, &E::Fr::multiplicative_generator());

        debug_assert!(get_degree::<E::Fr>(&t_poly) <= 3*n);

        let mut t_poly_parts = t_poly.break_into_multiples(required_domain_size)?;

        t_poly_parts.pop().expect("last part is irrelevant");
        let t_poly_high = t_poly_parts.pop().expect("high exists");
        let t_poly_mid = t_poly_parts.pop().expect("mid exists");
        let t_poly_low = t_poly_parts.pop().expect("low exists");

        let t_poly_high_commitment_data = Self::commit_single_poly(&t_poly_high, &bases, &worker)?;
        let t_poly_mid_commitment_data = Self::commit_single_poly(&t_poly_mid, &bases, &worker)?;
        let t_poly_low_commitment_data = Self::commit_single_poly(&t_poly_low, &bases, &worker)?;

        transcript.commit_bytes(t_poly_low_commitment_data.into_compressed().as_ref());
        transcript.commit_bytes(t_poly_mid_commitment_data.into_compressed().as_ref());
        transcript.commit_bytes(t_poly_high_commitment_data.into_compressed().as_ref());

        let z = transcript.get_challenge();

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

        let z_1_at_z = z_1.evaluate_at(&worker, z);
        let z_2_at_z = z_2.evaluate_at(&worker, z);

        let z_1_shifted_at_z = z_1_shifted.evaluate_at(&worker, z);
        let z_2_shifted_at_z = z_2_shifted.evaluate_at(&worker, z);

        let t_low_at_z = t_poly_low.evaluate_at(&worker, z);
        let t_mid_at_z = t_poly_mid.evaluate_at(&worker, z);
        let t_high_at_z = t_poly_high.evaluate_at(&worker, z);

        let l_0_at_z = l_0.evaluate_at(&worker, z);
        let l_n_minus_one_at_z = l_n_minus_one.evaluate_at(&worker, z);

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

            transcript.commit_field_element(&t_low_at_z);
            transcript.commit_field_element(&t_mid_at_z);
            transcript.commit_field_element(&t_high_at_z);

            transcript.commit_field_element(&z_1_at_z);
            transcript.commit_field_element(&z_2_at_z);

            transcript.commit_field_element(&z_1_shifted_at_z);
            transcript.commit_field_element(&z_2_shifted_at_z);
        }

        // let aggregation_challenge = transcript.get_challenge();

        let z_in_pow_of_domain_size = z.pow([required_domain_size as u64]);

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

            let mut t_at_z = E::Fr::zero();
            t_at_z.add_assign(&t_low_at_z);

            let mut tmp = z_in_pow_of_domain_size;
            tmp.mul_assign(&t_mid_at_z);
            t_at_z.add_assign(&tmp);

            let mut tmp = z_in_pow_of_domain_size;
            tmp.mul_assign(&z_in_pow_of_domain_size);
            tmp.mul_assign(&t_high_at_z);
            t_at_z.add_assign(&tmp);

            if t_at_z != t_1 {
                println!("Sanity check failed, may be due to public inputs ignored");
            }

            // assert_eq!(t_at_z, t_1, "sanity check failed");
        }

        // Compute linearization polynomial

        let mut linearization_poly = q_m.clone();
        let mut linearization_multiplier = alpha;
        {
            let mut tmp = q_l_at_z;
            tmp.mul_assign(&q_r_at_z);

            linearization_poly.scale(&worker, tmp);

            linearization_poly.add_assign_scaled(&worker, &q_l, &q_l_at_z);

            linearization_poly.add_assign_scaled(&worker, &q_r, &q_r_at_z);

            linearization_poly.add_assign_scaled(&worker, &q_o, &q_o_at_z);

            linearization_poly.add_assign(&worker, &q_c);

            linearization_poly.scale(&worker, linearization_multiplier);
        }

        linearization_multiplier.mul_assign(&alpha);
        {
            let mut factor = linearization_multiplier;
            let mut tmp = s_id_at_z;
            tmp.mul_assign(&beta);
            tmp.add_assign(&gamma);
            tmp.add_assign(&a_at_z);

            factor.mul_assign(&tmp);

            let mut tmp = s_id_at_z;
            tmp.add_assign(&n_fe);
            tmp.mul_assign(&beta);
            tmp.add_assign(&gamma);
            tmp.add_assign(&b_at_z);

            factor.mul_assign(&tmp);

            let mut tmp = s_id_at_z;
            tmp.add_assign(&two_n_fe);
            tmp.mul_assign(&beta);
            tmp.add_assign(&gamma);
            tmp.add_assign(&c_at_z);

            factor.mul_assign(&tmp);

            linearization_poly.add_assign_scaled(&worker, &z_1, &tmp);
        }

        linearization_multiplier.mul_assign(&alpha);
        {
            let mut factor = linearization_multiplier;
            let mut tmp = sigma_1_at_z;
            tmp.mul_assign(&beta);
            tmp.add_assign(&gamma);
            tmp.add_assign(&a_at_z);

            factor.mul_assign(&tmp);

            let mut tmp = sigma_2_at_z;
            tmp.mul_assign(&beta);
            tmp.add_assign(&gamma);
            tmp.add_assign(&b_at_z);

            factor.mul_assign(&tmp);

            let mut tmp = sigma_3_at_z;
            tmp.mul_assign(&beta);
            tmp.add_assign(&gamma);
            tmp.add_assign(&c_at_z);

            factor.mul_assign(&tmp);

            linearization_poly.add_assign_scaled(&worker, &z_2, &tmp);
        }

        linearization_multiplier.mul_assign(&alpha);
        linearization_multiplier.mul_assign(&alpha);
        {
            let mut tmp = z_1.clone();
            tmp.sub_assign(&worker, &z_2);
            linearization_poly.add_assign_scaled(&worker, &tmp, &linearization_multiplier);
        }

        let linearization_poly_at_z = linearization_poly.evaluate_at(&worker, z);

        transcript.commit_field_element(&linearization_poly_at_z);

        let mut z_by_omega = z;
        z_by_omega.mul_assign(&z_1.omega);

        let request_at_z = OpeningRequest {
            polynomials: vec![
                &a_poly,
                &b_poly,
                &c_poly,
                &z_1,
                &z_2,
                &s_id,
                &sigma_1,
                &sigma_2,
                &sigma_3,
                &t_poly_low,
                &t_poly_mid,
                &t_poly_high
            ],
            opening_point: z,
            opening_values: vec![
                a_at_z,
                b_at_z,
                c_at_z,
                z_1_at_z,
                z_2_at_z,
                s_id_at_z,
                sigma_1_at_z,
                sigma_2_at_z,
                sigma_3_at_z,
                t_low_at_z,
                t_mid_at_z,
                t_high_at_z,
            ]
        };

        let request_at_z_omega = OpeningRequest {
            polynomials: vec![
                &z_1,
                &z_2
            ],
            opening_point: z_by_omega,
            opening_values: vec![
                z_1_shifted_at_z,
                z_2_shifted_at_z,
            ]
        };

        let _ = Self::multiopening(request_at_z, &bases, &worker, &mut transcript);
        let _ = Self::multiopening(request_at_z_omega, &bases, &worker, &mut transcript);


        Ok(())

        
        // let proof = PlonkChunkedNonhomomorphicProof::<E, S> {
        //     a_opening_value: a_at_z,
        //     b_opening_value: b_at_z,
        //     c_opening_value: c_at_z,
        //     q_l_opening_value: q_l_at_z,
        //     q_r_opening_value: q_r_at_z,
        //     q_o_opening_value: q_o_at_z,
        //     q_m_opening_value: q_m_at_z,
        //     q_c_opening_value: q_c_at_z,
        //     s_id_opening_value: s_id_at_z,
        //     sigma_1_opening_value: sigma_1_at_z,
        //     sigma_2_opening_value: sigma_2_at_z,
        //     sigma_3_opening_value: sigma_3_at_z,
        //     z_1_unshifted_opening_value: z_1_at_z,
        //     z_2_unshifted_opening_value: z_2_at_z,
        //     z_1_shifted_opening_value: z_1_shifted_at_z,
        //     z_2_shifted_opening_value: z_2_shifted_at_z,
        //     t_low_opening_value: t_low_at_z,
        //     t_mid_opening_value: t_mid_at_z,
        //     t_high_opening_value: t_high_at_z,
        //     a_commitment: a_commitment,
        //     b_commitment: b_commitment,
        //     c_commitment: c_commitment,
        //     z_1_commitment: z_1_commitment,
        //     z_2_commitment: z_2_commitment,
        //     t_low_commitment: t_low_commitment,
        //     t_mid_commitment: t_mid_commitment,
        //     t_high_commitment: t_high_commitment,
        //     openings_proof: multiopen_proof,
        // };

        // Ok(proof)
    }
}

#[cfg(test)]
mod test {

    use crate::plonk::cs::*;
    use crate::pairing::Engine;
    use crate::SynthesisError;
    use super::*;
    use super::super::generator::*;

    use crate::ff::{Field, PrimeField};

    #[derive(Clone)]
    struct BenchmarkCircuit<E: Engine>{
        num_steps: usize,
        _marker: std::marker::PhantomData<E>
    }

    impl<E: Engine> Circuit<E> for BenchmarkCircuit<E> {
        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            // yeah, fibonacci...

            let one = E::Fr::one();
            let mut negative_one = one;
            negative_one.negate();

            let mut two = one;
            two.double();
            
            let mut a = cs.alloc(|| {
                Ok(E::Fr::one())
            })?;

            let mut b = cs.alloc(|| {
                Ok(E::Fr::one())
            })?;

            cs.enforce_zero_2((a, b), (one, negative_one))?;
            // cs.enforce_zero_2((b, CS::ONE), (one, negative_one))?;

            let mut c = cs.alloc(|| {
                Ok(two)
            })?;

            cs.enforce_zero_3((a, b, c), (one, one, negative_one))?;

            let mut a_value = one;
            let mut b_value = one;
            let mut c_value = two;

            for _ in 0..self.num_steps {
                a = b;
                b = c;

                a_value = b_value;
                b_value = c_value;
                c_value.add_assign(&a_value);

                c = cs.alloc(|| {
                    Ok(c_value)
                })?;

                cs.enforce_zero_3((a, b, c), (one, one, negative_one))?;
            }

            Ok(())
        }
    }

    #[test]
    fn test_bench_plonk_bls12() {
        use crate::pairing::Engine;
        use crate::pairing::{CurveProjective, CurveAffine};
        use crate::pairing::bls12_381::{Bls12, Fr};
        use crate::plonk::utils::*;
        use crate::multicore::Worker;
        // use crate::plonk::tester::*;

        type Transcr = Blake2sTranscript<Fr>;
        type Eng = Bls12;

        use std::time::Instant;

        use crate::plonk::fft::cooley_tukey_ntt::*;
        use crate::plonk::commitments::transparent::fri::coset_combining_fri::precomputation::*;

        let sizes: Vec<usize> = vec![(1 << 18) - 10, (1 << 19) - 10, (1 << 20) - 10, (1 << 21) - 10, (1 << 22) - 10, (1 << 23) - 10];

        let max_size = *sizes.last().unwrap();

        let worker = Worker::new();

        println!("Making bases");
        let bases = {
            use crate::pairing::Wnaf;
            let tau = Fr::from_str("42").unwrap();
            let powers_of_tau = vec![Fr::one(); max_size.next_power_of_two()];
            let mut powers_of_tau = Polynomial::<Fr, _>::from_coeffs(powers_of_tau).unwrap();

            powers_of_tau.distribute_powers(&worker, tau);

            let powers_of_tau = powers_of_tau.into_coeffs();

            // Compute G1 window table
            let mut g1_wnaf = Wnaf::new();
            let g1 = <Eng as Engine>::G1::one();
            let g1_wnaf = g1_wnaf.base(g1, max_size.next_power_of_two());

            let mut bases = vec![g1; max_size.next_power_of_two()];

            // Compute the H query with multiple threads
            worker.scope(bases.len(), |scope, chunk| {
                for (h, p) in bases.chunks_mut(chunk).zip(powers_of_tau.chunks(chunk))
                {
                    let mut g1_wnaf = g1_wnaf.shared();
                    scope.spawn(move |_| {
                        // Set values of the H query to g1^{(tau^i * t(tau)) / delta}
                        for (h, p) in h.iter_mut().zip(p.iter())
                        {
                            // Exponentiate
                            *h = g1_wnaf.scalar(p.into_repr());
                        }

                        // Batch normalize
                        <<Eng as Engine>::G1 as CurveProjective>::batch_normalization(h);
                    });
                }
            });

            bases.iter().map(|el| el.into_affine()).collect::<Vec<_>>()
        };
        println!("Done making bases");

        for size in sizes.into_iter() {

            let circuit = BenchmarkCircuit::<Eng> {
                // num_steps: 1_000_000,
                num_steps: size,
                _marker: std::marker::PhantomData
            };

            let omegas_bitreversed = BitReversedOmegas::<Fr>::new_for_domain_size(size.next_power_of_two());
            let omegas_inv_bitreversed = <OmegasInvBitreversed::<Fr> as CTPrecomputations::<Fr>>::new_for_domain_size(size.next_power_of_two());

            println!("Start setup and precomputations");
            let (_, setup_precomp) = setup_with_precomputations::<Eng, _, _>(
                &circuit,
                &omegas_bitreversed,
                &bases[0..size.next_power_of_two()]
            ).unwrap();

            let mut prover = ProvingAssembly::<Eng>::new();
            circuit.synthesize(&mut prover).unwrap();
            prover.finalize();

            println!("End setup and precomputations");

            println!("Start proving");

            let start = Instant::now();

            let _ = prover.prove_with_setup_precomputed::<_, _, Transcr>(
                &setup_precomp, 
                &worker, 
                &omegas_bitreversed, 
                &omegas_inv_bitreversed,
                &bases[0..size.next_power_of_two()]
            ).unwrap();

            println!("Proving taken {:?} for size {}", start.elapsed(), size);
        }


        // {
        //     let mut tester = TestingAssembly::<Transparent252>::new();

        //     circuit.synthesize(&mut tester).expect("must synthesize");

        //     let satisfied = tester.is_satisfied();

        //     assert!(satisfied);

        //     println!("Circuit is satisfied");
        // }

        // println!("Start setup");
        // let start = Instant::now();
        // let (setup, aux) = setup::<Transparent252, Committer, _>(&circuit, meta.clone()).unwrap();
        // println!("Setup taken {:?}", start.elapsed());

        // println!("Using circuit with N = {}", setup.n);

        // println!("Start proving");
        // let start = Instant::now();
        // let proof = prove_nonhomomorphic_chunked::<Transparent252, Committer, Blake2sTranscript::<Fr>, _>(&circuit, &aux, meta.clone()).unwrap();
        // println!("Proof taken {:?}", start.elapsed());

        // println!("Start verifying");
        // let start = Instant::now();
        // let valid = verify_nonhomomorphic_chunked::<Transparent252, Committer, Blake2sTranscript::<Fr>>(&setup, &proof, meta).unwrap();
        // println!("Verification with unnecessary precomputation taken {:?}", start.elapsed());

        // assert!(valid);
    }

    #[test]
    fn test_bench_plonk_bn254() {
        use crate::pairing::Engine;
        use crate::pairing::{CurveProjective, CurveAffine};
        use crate::pairing::bn256::{Bn256, Fr};
        use crate::plonk::utils::*;
        use crate::multicore::Worker;
        // use crate::plonk::tester::*;

        type Transcr = Blake2sTranscript<Fr>;
        type Eng = Bn256;

        use std::time::Instant;

        use crate::plonk::fft::cooley_tukey_ntt::*;
        use crate::plonk::commitments::transparent::fri::coset_combining_fri::precomputation::*;

        let sizes: Vec<usize> = vec![(1 << 18) - 10, (1 << 19) - 10, (1 << 20) - 10, (1 << 21) - 10, (1 << 22) - 10, (1 << 23) - 10];

        let max_size = *sizes.last().unwrap();

        let worker = Worker::new();

        println!("Making bases");
        let bases = {
            use crate::pairing::Wnaf;
            let tau = Fr::from_str("42").unwrap();
            let powers_of_tau = vec![Fr::one(); max_size.next_power_of_two()];
            let mut powers_of_tau = Polynomial::<Fr, _>::from_coeffs(powers_of_tau).unwrap();

            powers_of_tau.distribute_powers(&worker, tau);

            let powers_of_tau = powers_of_tau.into_coeffs();

            // Compute G1 window table
            let mut g1_wnaf = Wnaf::new();
            let g1 = <Eng as Engine>::G1::one();
            let g1_wnaf = g1_wnaf.base(g1, max_size.next_power_of_two());

            let mut bases = vec![g1; max_size.next_power_of_two()];

            // Compute the H query with multiple threads
            worker.scope(bases.len(), |scope, chunk| {
                for (h, p) in bases.chunks_mut(chunk).zip(powers_of_tau.chunks(chunk))
                {
                    let mut g1_wnaf = g1_wnaf.shared();
                    scope.spawn(move |_| {
                        // Set values of the H query to g1^{(tau^i * t(tau)) / delta}
                        for (h, p) in h.iter_mut().zip(p.iter())
                        {
                            // Exponentiate
                            *h = g1_wnaf.scalar(p.into_repr());
                        }

                        // Batch normalize
                        <<Eng as Engine>::G1 as CurveProjective>::batch_normalization(h);
                    });
                }
            });

            bases.iter().map(|el| el.into_affine()).collect::<Vec<_>>()
        };
        println!("Done making bases");

        for size in sizes.into_iter() {
            println!("Working for size {}", size);

            let circuit = BenchmarkCircuit::<Eng> {
                // num_steps: 1_000_000,
                num_steps: size,
                _marker: std::marker::PhantomData
            };

            let omegas_bitreversed = BitReversedOmegas::<Fr>::new_for_domain_size(size.next_power_of_two());
            let omegas_inv_bitreversed = <OmegasInvBitreversed::<Fr> as CTPrecomputations::<Fr>>::new_for_domain_size(size.next_power_of_two());

            println!("Start setup and precomputations");
            let (_, setup_precomp) = setup_with_precomputations::<Eng, _, _>(
                &circuit,
                &omegas_bitreversed,
                &bases[0..size.next_power_of_two()]
            ).unwrap();

            let mut prover = ProvingAssembly::<Eng>::new();
            circuit.synthesize(&mut prover).unwrap();
            prover.finalize();

            println!("End setup and precomputations");

            println!("Start proving");

            let start = Instant::now();

            let _ = prover.prove_with_setup_precomputed::<_, _, Transcr>(
                &setup_precomp, 
                &worker, 
                &omegas_bitreversed, 
                &omegas_inv_bitreversed,
                &bases[0..size.next_power_of_two()]
            ).unwrap();

            println!("Proving taken {:?} for size {}", start.elapsed(), size);
        }


        // {
        //     let mut tester = TestingAssembly::<Transparent252>::new();

        //     circuit.synthesize(&mut tester).expect("must synthesize");

        //     let satisfied = tester.is_satisfied();

        //     assert!(satisfied);

        //     println!("Circuit is satisfied");
        // }

        // println!("Start setup");
        // let start = Instant::now();
        // let (setup, aux) = setup::<Transparent252, Committer, _>(&circuit, meta.clone()).unwrap();
        // println!("Setup taken {:?}", start.elapsed());

        // println!("Using circuit with N = {}", setup.n);

        // println!("Start proving");
        // let start = Instant::now();
        // let proof = prove_nonhomomorphic_chunked::<Transparent252, Committer, Blake2sTranscript::<Fr>, _>(&circuit, &aux, meta.clone()).unwrap();
        // println!("Proof taken {:?}", start.elapsed());

        // println!("Start verifying");
        // let start = Instant::now();
        // let valid = verify_nonhomomorphic_chunked::<Transparent252, Committer, Blake2sTranscript::<Fr>>(&setup, &proof, meta).unwrap();
        // println!("Verification with unnecessary precomputation taken {:?}", start.elapsed());

        // assert!(valid);
    }
}