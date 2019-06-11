use crate::pairing::{Engine};
use crate::sonic::cs::Backend;
use std::marker::PhantomData;
use crate::SynthesisError;
use crate::sonic::cs::SynthesisDriver;

use crate::sonic::cs::{Circuit, ConstraintSystem, Variable, LinearCombination};

use crate::pairing::ff::Field;

pub struct Preprocess<E: Engine> {
    pub k_map: Vec<usize>,
    pub n: usize,
    pub q: usize,
    _marker: PhantomData<E>
}

impl<'a, E: Engine> Backend<E> for &'a mut Preprocess<E> {
    type LinearConstraintIndex = ();

    fn get_for_q(&self, _q: usize) -> Self::LinearConstraintIndex { () }

    fn new_k_power(&mut self, index: usize) {
        self.k_map.push(index);
    }

    fn new_multiplication_gate(&mut self) {
        self.n += 1;
    }

    fn new_linear_constraint(&mut self) {
        self.q += 1;

        ()
    }
}

impl<E: Engine> Preprocess<E> {
    pub fn new() -> Self {
        Preprocess { 
            k_map: vec![], 
            n: 0, 
            q: 0, 
            _marker: PhantomData 
        }
    }
}

pub struct Wires<E: Engine> {
    pub a: Vec<E::Fr>,
    pub b: Vec<E::Fr>,
    pub c: Vec<E::Fr>
}

impl<'a, E: Engine> Backend<E> for &'a mut Wires<E> {
    type LinearConstraintIndex = ();

    fn new_linear_constraint(&mut self) -> Self::LinearConstraintIndex { () }

    fn get_for_q(&self, _q: usize) -> Self::LinearConstraintIndex { () }

    fn new_multiplication_gate(&mut self) {
        self.a.push(E::Fr::zero());
        self.b.push(E::Fr::zero());
        self.c.push(E::Fr::zero());
    }

    fn get_var(&self, variable: Variable) -> Option<E::Fr> {
        Some(match variable {
            Variable::A(index) => {
                self.a[index - 1]
            },
            Variable::B(index) => {
                self.b[index - 1]
            },
            Variable::C(index) => {
                self.c[index - 1]
            }
        })
    }

    fn set_var<F>(&mut self, variable: Variable, value: F) -> Result<(), SynthesisError>
        where F: FnOnce() -> Result<E::Fr, SynthesisError>
    {
        let value = value()?;

        match variable {
            Variable::A(index) => {
                self.a[index - 1] = value;
            },
            Variable::B(index) => {
                self.b[index - 1] = value;
            },
            Variable::C(index) => {
                self.c[index - 1] = value;
            }
        }

        Ok(())
    }
}

impl<E: Engine> Wires<E> {
    pub fn new() -> Self {
        Wires {
            a: vec![],
            b: vec![],
            c: vec![],
        }
    }
}

pub struct CountNandQ<S: SynthesisDriver> {
    pub n: usize,
    pub q: usize,
    _marker: std::marker::PhantomData<S>
}

impl<'a, E: Engine, S: SynthesisDriver> Backend<E> for &'a mut CountNandQ<S> {
    type LinearConstraintIndex = ();

    fn get_for_q(&self, _q: usize) -> Self::LinearConstraintIndex { () }

    fn new_multiplication_gate(&mut self) {
        self.n += 1;
    }

    fn new_linear_constraint(&mut self) -> Self::LinearConstraintIndex {
        self.q += 1;

        ()
    }
}

impl<S: SynthesisDriver> CountNandQ<S> {
    pub fn new() -> Self {
        Self {
            n: 0,
            q: 0,
            _marker: std::marker::PhantomData
        }
    }
}

pub struct CountN<S: SynthesisDriver> {
    pub n: usize,
    _marker: std::marker::PhantomData<S>
}

impl<'a, E: Engine, S: SynthesisDriver> Backend<E> for &'a mut CountN<S> {
    type LinearConstraintIndex = ();

    fn new_linear_constraint(&mut self) -> Self::LinearConstraintIndex { () }

    fn get_for_q(&self, _q: usize) -> Self::LinearConstraintIndex { () }

    fn new_multiplication_gate(&mut self) {
        self.n += 1;
    }
}

impl<S: SynthesisDriver> CountN<S> {
    pub fn new() -> Self {
        Self {
            n: 0,
            _marker: std::marker::PhantomData
        }
    }
}

