use crate::pairing::ff::{Field};
use crate::pairing::{Engine};

use crate::{SynthesisError};
use std::marker::PhantomData;

mod lc;
pub use self::lc::{Coeff, Variable, LinearCombination};

pub trait Circuit<E: Engine> {
    fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError>;
}

pub trait ConstraintSystem<E: Engine> {
    const ONE: Variable;

    fn alloc<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>;

    fn alloc_input<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>;

    fn enforce_zero(&mut self, lc: LinearCombination<E>);

    fn multiply<F>(&mut self, values: F) -> Result<(Variable, Variable, Variable), SynthesisError>
    where
        F: FnOnce() -> Result<(E::Fr, E::Fr, E::Fr), SynthesisError>;

    // TODO: get rid of this
    fn get_value(&self, _var: Variable) -> Result<E::Fr, ()> {
        Err(())
    }
}



/// This is a backend for the `SynthesisDriver` to relay information about
/// the concrete circuit. One backend might just collect basic information
/// about the circuit for verification, while another actually constructs
/// a witness.
pub trait Backend<E: Engine> {
    type LinearConstraintIndex;

    /// Get the value of a variable. Can return None if we don't know.
    fn get_var(&self, _variable: Variable) -> Option<E::Fr> { None }

    /// Set the value of a variable. Might error if this backend expects to know it.
    fn set_var<F>(&mut self, _variable: Variable, _value: F) -> Result<(), SynthesisError>
        where F: FnOnce() -> Result<E::Fr, SynthesisError> { Ok(()) }

    /// Create a new multiplication gate.
    fn new_multiplication_gate(&mut self) { }

    /// Create a new linear constraint, returning the power of Y for caching purposes.
    fn new_linear_constraint(&mut self) -> Self::LinearConstraintIndex;

    /// Insert a term into a linear constraint. TODO: bad name of function
    fn insert_coefficient(&mut self, _var: Variable, _coeff: Coeff<E>, _y: &Self::LinearConstraintIndex) { }

    /// Compute a `LinearConstraintIndex` from `q`.
    fn get_for_q(&self, q: usize) -> Self::LinearConstraintIndex;

    /// Mark y^{_index} as the power of y cooresponding to the public input
    /// coefficient for the next public input, in the k(Y) polynomial.
    fn new_k_power(&mut self, _index: usize) { }
}

/// This is an abstraction which synthesizes circuits.
pub trait SynthesisDriver {
    fn synthesize<E: Engine, C: Circuit<E>, B: Backend<E>>(backend: B, circuit: &C) -> Result<(), SynthesisError>;
}