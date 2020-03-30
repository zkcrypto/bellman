use crate::pairing::ff::{Field};
use crate::pairing::{Engine};

use crate::{SynthesisError};
use std::marker::PhantomData;

pub use crate::cs::{Variable, Index};
pub use Index::*;

pub trait Circuit<E: Engine> {
    fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError>;
}

pub trait ConstraintSystem<E: Engine> {

    // allocate a variable
    fn alloc<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>;

    // allocate an input variable
    fn alloc_input<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>;

    fn new_gate(&mut self, variables: (Variable, Variable, Variable), 
        coeffs: (E::Fr, E::Fr, E::Fr, E::Fr, E::Fr, E::Fr)) -> Result<(), SynthesisError>;

    fn get_value(&self, _variable: Variable) -> Result<E::Fr, SynthesisError> { 
        Err(SynthesisError::AssignmentMissing)
    }

    fn get_dummy_variable(&self) -> Variable;

    fn enforce_zero_2(&mut self, variables: (Variable, Variable), coeffs:(E::Fr, E::Fr)) -> Result<(), SynthesisError>
    {
        let (v_0, v_1) = variables;
        let (c_0, c_1) = coeffs;
        let zero = E::Fr::zero();

        self.new_gate((v_0, v_1, self.get_dummy_variable()), (c_0, c_1, zero, zero, zero, zero))
    }

    // allocate a linear combination gate
    fn enforce_zero_3(&mut self, variables: (Variable, Variable, Variable), coeffs:(E::Fr, E::Fr, E::Fr)) -> Result<(), SynthesisError>
    {
        let (v_0, v_1, v_2) = variables;
        let (c_0, c_1, c_2) = coeffs;
        let zero = E::Fr::zero();

        self.new_gate((v_0, v_1, v_2), (c_0, c_1, c_2, zero, zero, zero))       
    }
}
