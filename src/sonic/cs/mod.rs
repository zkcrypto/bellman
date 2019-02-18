extern crate ff;
extern crate pairing;

use ff::{Field};
use pairing::{Engine};

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
    /// Get the value of a variable. Can return None if we don't know.
    fn get_var(&self, _variable: Variable) -> Option<E::Fr> { None }

    /// Set the value of a variable. Might error if this backend expects to know it.
    fn set_var<F>(&mut self, _variable: Variable, _value: F) -> Result<(), SynthesisError>
        where F: FnOnce() -> Result<E::Fr, SynthesisError> { Ok(()) }

    /// Create a new multiplication gate.
    fn new_multiplication_gate(&mut self) { }

    /// Create a new linear constraint.
    fn new_linear_constraint(&mut self) { }

    /// Insert a term into a linear constraint. TODO: bad name of function
    fn insert_coefficient(&mut self, _var: Variable, _coeff: Coeff<E>) { }

    /// Mark y^{_index} as the power of y cooresponding to the public input
    /// coefficient for the next public input, in the k(Y) polynomial.
    fn new_k_power(&mut self, _index: usize) { }
}

/// This is an abstraction which synthesizes circuits.
pub trait SynthesisDriver {
    fn synthesize<E: Engine, C: Circuit<E>, B: Backend<E>>(backend: B, circuit: &C) -> Result<(), SynthesisError>;
}

pub struct Basic;

impl SynthesisDriver for Basic {
    fn synthesize<E: Engine, C: Circuit<E>, B: Backend<E>>(backend: B, circuit: &C) -> Result<(), SynthesisError> {
        struct Synthesizer<E: Engine, B: Backend<E>> {
            backend: B,
            current_variable: Option<usize>,
            _marker: PhantomData<E>,
            q: usize,
            n: usize,
        }

        impl<E: Engine, B: Backend<E>> ConstraintSystem<E> for Synthesizer<E, B> {
            const ONE: Variable = Variable::A(1);

            fn alloc<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
            where
                F: FnOnce() -> Result<E::Fr, SynthesisError>
            {
                match self.current_variable.take() {
                    Some(index) => {
                        let var_a = Variable::A(index);
                        let var_b = Variable::B(index);
                        let var_c = Variable::C(index);

                        let mut product = None;

                        let value_a = self.backend.get_var(var_a);

                        self.backend.set_var(var_b, || {
                            let value_b = value()?;
                            product = Some(value_a.ok_or(SynthesisError::AssignmentMissing)?);
                            product.as_mut().map(|product| product.mul_assign(&value_b));

                            Ok(value_b)
                        })?;

                        self.backend.set_var(var_c, || {
                            product.ok_or(SynthesisError::AssignmentMissing)
                        })?;

                        self.current_variable = None;

                        Ok(var_b)
                    },
                    None => {
                        self.n += 1;
                        let index = self.n;
                        self.backend.new_multiplication_gate();

                        let var_a = Variable::A(index);

                        self.backend.set_var(var_a, value)?;

                        self.current_variable = Some(index);

                        Ok(var_a)
                    }
                }
            }

            fn alloc_input<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
            where
                F: FnOnce() -> Result<E::Fr, SynthesisError>
            {
                let input_var = self.alloc(value)?;

                self.enforce_zero(LinearCombination::zero() + input_var);
                self.backend.new_k_power(self.q);

                Ok(input_var)
            }

            fn enforce_zero(&mut self, lc: LinearCombination<E>)
            {
                self.q += 1;
                self.backend.new_linear_constraint();

                for (var, coeff) in lc.as_ref() {
                    self.backend.insert_coefficient(*var, *coeff);
                }
            }

            fn multiply<F>(&mut self, values: F) -> Result<(Variable, Variable, Variable), SynthesisError>
            where
                F: FnOnce() -> Result<(E::Fr, E::Fr, E::Fr), SynthesisError>
            {
                self.n += 1;
                let index = self.n;
                self.backend.new_multiplication_gate();

                let a = Variable::A(index);
                let b = Variable::B(index);
                let c = Variable::C(index);

                let mut b_val = None;
                let mut c_val = None;

                self.backend.set_var(a, || {
                    let (a, b, c) = values()?;

                    b_val = Some(b);
                    c_val = Some(c);

                    Ok(a)
                })?;

                self.backend.set_var(b, || {
                    b_val.ok_or(SynthesisError::AssignmentMissing)
                })?;

                self.backend.set_var(c, || {
                    c_val.ok_or(SynthesisError::AssignmentMissing)
                })?;

                Ok((a, b, c))
            }

            fn get_value(&self, var: Variable) -> Result<E::Fr, ()> {
                self.backend.get_var(var).ok_or(())
            }
        }

        let mut tmp: Synthesizer<E, B> = Synthesizer {
            backend: backend,
            current_variable: None,
            _marker: PhantomData,
            q: 0,
            n: 0,
        };

        let one = tmp.alloc_input(|| Ok(E::Fr::one())).expect("should have no issues");

        match (one, <Synthesizer<E, B> as ConstraintSystem<E>>::ONE) {
            (Variable::A(1), Variable::A(1)) => {},
            _ => panic!("one variable is incorrect")
        }

        circuit.synthesize(&mut tmp)?;

        // let blindings_to_add = 6;

        // for i in 0..blindings_to_add {

        //     match tmp.current_variable.take() {
        //         Some(index) => {
        //             let var_a = Variable::A(index);
        //             let var_b = Variable::B(index);
        //             let var_c = Variable::C(index);

        //             let mut product = None;

        //             let value_a = tmp.backend.get_var(var_a);

        //             tmp.backend.set_var(var_b, || {
        //                 let value_b = E::Fr::one();
        //                 product = Some(value_a.ok_or(SynthesisError::AssignmentMissing)?);
        //                 product.as_mut().map(|product| product.mul_assign(&value_b));

        //                 Ok(value_b)
        //             })?;

        //             tmp.backend.set_var(var_c, || {
        //                 product.ok_or(SynthesisError::AssignmentMissing)
        //             })?;

        //             tmp.current_variable = None;
        //         },
        //         None => {
        //             self.n += 1;
        //             let index = self.n ;
        //             tmp.backend.new_multiplication_gate();

        //             let var_a = Variable::A(index);

        //             tmp.backend.set_var(var_a, value)?;

        //             tmp.current_variable = Some(index);
        //         }
        //     }
        // }

        // TODO: add blinding factors so we actually get zero-knowledge

        Ok(())
    }
}

pub struct Nonassigning;

impl SynthesisDriver for Nonassigning {
    fn synthesize<E: Engine, C: Circuit<E>, B: Backend<E>>(backend: B, circuit: &C) -> Result<(), SynthesisError> {
        struct NonassigningSynthesizer<E: Engine, B: Backend<E>> {
                backend: B,
                current_variable: Option<usize>,
                _marker: PhantomData<E>,
                q: usize,
                n: usize,
            }

            impl<E: Engine, B: Backend<E>> ConstraintSystem<E> for NonassigningSynthesizer<E, B> {
                const ONE: Variable = Variable::A(1);

                fn alloc<F>(&mut self, _value: F) -> Result<Variable, SynthesisError>
                where
                    F: FnOnce() -> Result<E::Fr, SynthesisError>
                {
                    match self.current_variable.take() {
                        Some(index) => {
                            let var_b = Variable::B(index);

                            self.current_variable = None;

                            Ok(var_b)
                        },
                        None => {
                            self.n += 1;
                            let index = self.n;
                            self.backend.new_multiplication_gate();

                            let var_a = Variable::A(index);

                            self.current_variable = Some(index);

                            Ok(var_a)
                        }
                    }
                }

                fn alloc_input<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
                where
                    F: FnOnce() -> Result<E::Fr, SynthesisError>
                {
                    let input_var = self.alloc(value)?;

                    self.enforce_zero(LinearCombination::zero() + input_var);
                    self.backend.new_k_power(self.q);

                    Ok(input_var)
                }

                fn enforce_zero(&mut self, lc: LinearCombination<E>)
                {
                    self.q += 1;
                    self.backend.new_linear_constraint();

                    for (var, coeff) in lc.as_ref() {
                        self.backend.insert_coefficient(*var, *coeff);
                    }
                }

                fn multiply<F>(&mut self, _values: F) -> Result<(Variable, Variable, Variable), SynthesisError>
                where
                    F: FnOnce() -> Result<(E::Fr, E::Fr, E::Fr), SynthesisError>
                {
                    self.n += 1;
                    let index = self.n;
                    self.backend.new_multiplication_gate();

                    let a = Variable::A(index);
                    let b = Variable::B(index);
                    let c = Variable::C(index);

                    Ok((a, b, c))
                }

                fn get_value(&self, var: Variable) -> Result<E::Fr, ()> {
                    self.backend.get_var(var).ok_or(())
                }
            }

            let mut tmp: NonassigningSynthesizer<E, B> = NonassigningSynthesizer {
                backend: backend,
                current_variable: None,
                _marker: PhantomData,
                q: 0,
                n: 0,
            };

            let one = tmp.alloc_input(|| Ok(E::Fr::one())).expect("should have no issues");

            match (one, <NonassigningSynthesizer<E, B> as ConstraintSystem<E>>::ONE) {
                (Variable::A(1), Variable::A(1)) => {},
                _ => panic!("one variable is incorrect")
            }

            circuit.synthesize(&mut tmp)?;

            // TODO: add blinding factors so we actually get zero-knowledge

            // println!("n = {}", tmp.n);

            Ok(())
    }
}