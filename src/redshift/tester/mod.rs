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
use crate::plonk::generator::*;


#[derive(Debug)]
pub struct TestingAssembly<E: Engine> {
    m: usize,
    n: usize,
    input_gates: Vec<Gate<E>>,
    aux_gates: Vec<Gate<E>>,

    num_inputs: usize,
    num_aux: usize,

    input_assingments: Vec<E::Fr>,
    aux_assingments: Vec<E::Fr>,

    inputs_map: Vec<usize>,

    is_finalized: bool
}

impl<E: Engine> ConstraintSystem<E> for TestingAssembly<E> {
    const ZERO: Variable = Variable(Index::Aux(1));
    const ONE: Variable = Variable(Index::Aux(2));

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

        let gate = Gate::<E>::new_enforce_constant_gate(input_var, Some(E::Fr::zero()), self.dummy_variable());
        // let gate = Gate::<E>::new_enforce_constant_gate(input_var, Some(value), self.dummy_variable());
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

impl<E: Engine> TestingAssembly<E> {
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

    pub fn num_gates(&self) -> usize {
        assert!(self.is_finalized);

        self.input_gates.len() + self.aux_gates.len()
    }

    fn finalize(&mut self) {
        if self.is_finalized {
            return;
        }
        let n = self.input_gates.len() + self.aux_gates.len();
        if (n+1).is_power_of_two() {
            return;
        }

        let empty_gate = Gate::<E>::new_empty_gate(self.dummy_variable());

        let new_aux_len = (n+1).next_power_of_two() - 1 - self.input_gates.len();

        self.aux_gates.resize(new_aux_len, empty_gate);

        self.is_finalized = true;
    }

    fn get_value(&self, var: &Variable) -> E::Fr {
        match var {
            Variable(Index::Input(input)) => {
                self.input_assingments[*input - 1]
            },
            Variable(Index::Aux(aux)) => {
                self.aux_assingments[*aux - 1]
            }
        }
    }

    pub fn is_satisfied(mut self) -> bool {
        self.finalize();
        assert!(self.is_finalized);

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
        for (i, gate) in self.input_gates.iter().enumerate()
        {
            let q_l = coeff_into_field_element(&gate.q_l);
            let q_r = coeff_into_field_element(&gate.q_r);
            let q_o = coeff_into_field_element(&gate.q_o);
            let q_m = coeff_into_field_element(&gate.q_m);
            let q_c = coeff_into_field_element(&gate.q_c);

            let a_value = self.get_value(gate.a_wire());
            let b_value = self.get_value(gate.b_wire());
            let c_value = self.get_value(gate.c_wire());

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
                println!("Unsatisfied at input gate {}", i+1);
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

            let a_value = self.get_value(gate.a_wire());
            let b_value = self.get_value(gate.b_wire());
            let c_value = self.get_value(gate.c_wire());

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
}