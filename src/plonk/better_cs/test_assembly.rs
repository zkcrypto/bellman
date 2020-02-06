use crate::pairing::ff::{Field, PrimeField};
use crate::pairing::{Engine};

use crate::{SynthesisError};
use std::marker::PhantomData;

use super::cs::*;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Gate<F: PrimeField> {
    varialbes: [Variable; 3],
    coefficients: [F; 6],
}

impl<F: PrimeField> Gate<F> {
    pub fn new_gate(variables:(Variable, Variable, Variable), coeffs: [F; 6]) -> Self {
        Self {
            varialbes: [variables.0, variables.1, variables.2],
            coefficients: coeffs
        }
    }
}

#[derive(Debug, Clone)]
pub struct TestAssembly<E: Engine> {
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

impl<E: Engine> ConstraintSystem<E> for TestAssembly<E> {
    type GateCoefficients = [E::Fr; 6];

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

        let zero = E::Fr::zero();

        let gate_coeffs = [E::Fr::one(), zero, zero, zero, zero, zero];

        let dummy = self.get_dummy_variable();

        let gate = Gate::<E::Fr>::new_gate((input_var, dummy, dummy), gate_coeffs);

        self.input_gates.push(gate);

        // println!("Allocated input Input({}) with value {}", index, value);

        Ok(input_var)

    }

    // allocate an abstract gate
    fn new_gate(&mut self, variables: (Variable, Variable, Variable), 
        coeffs: Self::GateCoefficients) -> Result<(), SynthesisError>
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

    fn get_value(&self, var: Variable) -> Result<E::Fr, SynthesisError> {
        let value = match var {
            Variable(Index::Aux(0)) => {
                return Err(SynthesisError::AssignmentMissing);
            }
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

impl<E: Engine> TestAssembly<E> {
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

        let dummy_value = E::Fr::zero();

        let zero = E::Fr::zero();
        let one = E::Fr::one();
        let mut minus_one = one;
        minus_one.negate();

        // let dummy_var = tmp.alloc(|| Ok(dummy_value)).expect("must allocate a dummy variable");
        // tmp.new_gate((dummy_var, dummy_var, dummy_var), [one, zero, zero, zero, minus_one, zero]).expect("should enforce a dummy variable");;

        // match (tmp.dummy_variable(), dummy_var) {
        //     (Variable(Index::Aux(1)), Variable(Index::Aux(1))) => {},
        //     _ => panic!("dummy variable is incorrect")
        // }

        tmp
    }

    // return variable that is not in a constraint formally, but has some value
    fn dummy_variable(&self) -> Variable {
        Variable(Index::Aux(0))
    }
}
