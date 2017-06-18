#![feature(i128_type)]

extern crate rand;
extern crate num_cpus;
extern crate crossbeam;
extern crate byteorder;
extern crate serde;

pub mod curves;
pub mod groth16;

use std::collections::HashMap;
use std::ops;
use std::ops::Deref;
use std::borrow::Borrow;

use curves::{Engine, Field};

#[derive(Copy, Clone)]
pub struct Variable(Index);

impl Variable {
    pub fn one() -> Self {
        Variable(Index::Input(0))
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Index {
    Input(usize),
    Aux(usize)
}

pub struct LinearCombination<'a, E: Engine + 'a>(HashMap<Index, E::Fr>, &'a E);

impl<'a, E: Engine + 'a> ops::Add<Variable> for LinearCombination<'a, E> {
    type Output = LinearCombination<'a, E>;

    fn add(self, other: Variable) -> LinearCombination<'a, E> {
        let one = E::Fr::one(self.1);

        self.add(one, other)
    }
}

impl<'a, E: Engine + 'a> ops::Add<(E::Fr, Variable)> for LinearCombination<'a, E> {
    type Output = LinearCombination<'a, E>;

    fn add(self, (coeff, var): (E::Fr, Variable)) -> LinearCombination<'a, E> {
        self.add(coeff, var)
    }
}

impl<'a, E: Engine + 'a> ops::Sub<Variable> for LinearCombination<'a, E> {
    type Output = LinearCombination<'a, E>;

    fn sub(self, other: Variable) -> LinearCombination<'a, E> {
        let one = E::Fr::one(self.1);

        self.sub(one, other)
    }
}

impl<'a, E: Engine + 'a> ops::Sub<(E::Fr, Variable)> for LinearCombination<'a, E> {
    type Output = LinearCombination<'a, E>;

    fn sub(self, (coeff, var): (E::Fr, Variable)) -> LinearCombination<'a, E> {
        self.sub(coeff, var)
    }
}

impl<'a, E: Engine> LinearCombination<'a, E> {
    pub fn zero(e: &'a E) -> LinearCombination<'a, E> {
        LinearCombination(HashMap::new(), e)
    }

    pub fn one(e: &'a E) -> LinearCombination<'a, E> {
        LinearCombination::zero(e).add(E::Fr::one(e), Variable::one())
    }

    pub fn add(mut self, coeff: E::Fr, var: Variable) -> Self
    {
        self.0.entry(var.0)
              .or_insert(E::Fr::zero())
              .add_assign(self.1, &coeff);

        self
    }

    pub fn sub(self, mut coeff: E::Fr, var: Variable) -> Self
    {
        coeff.negate(self.1);

        self.add(coeff, var)
    }

    fn evaluate(
        &self,
        e: &E,
        input_assignment: &[E::Fr],
        aux_assignment: &[E::Fr]
    ) -> E::Fr
    {
        let mut acc = E::Fr::zero();
        for (index, coeff) in self.0.iter() {
            let mut n = *coeff;
            match index {
                &Index::Input(id) => {
                    n.mul_assign(e, &input_assignment[id]);
                },
                &Index::Aux(id) => {
                    n.mul_assign(e, &aux_assignment[id]);
                }
            }
            acc.add_assign(e, &n);
        }

        acc
    }
}

pub trait Circuit<E: Engine> {
    type InputMap: Input<E>;

    /// Synthesize the circuit into a rank-1 quadratic constraint system
    #[must_use]
    fn synthesize<CS: ConstraintSystem<E>>(self, engine: &E, cs: &mut CS) -> Self::InputMap;
}

pub trait Input<E: Engine> {
    /// Synthesize the circuit, except with additional access to public input
    /// variables
    fn synthesize<CS: PublicConstraintSystem<E>>(self, engine: &E, cs: &mut CS);
}

pub trait PublicConstraintSystem<E: Engine>: ConstraintSystem<E> {
    /// Allocate a public input that the verifier knows.
    fn alloc_input(&mut self, value: E::Fr) -> Variable;
}

pub trait ConstraintSystem<E: Engine> {
    /// Allocate a private variable in the constraint system, setting it to
    /// the provided value.
    fn alloc(&mut self, value: E::Fr) -> Variable;
    
    /// Enforce that `A` * `B` = `C`.
    fn enforce(
        &mut self,
        a: LinearCombination<E>,
        b: LinearCombination<E>,
        c: LinearCombination<E>
    );
}

pub enum Cow<'a, T: 'a> {
    Owned(T),
    Borrowed(&'a T)
}

impl<'a, T: 'a> Deref for Cow<'a, T> {
    type Target = T;

    fn deref(&self) -> &T {
        match *self {
            Cow::Owned(ref v) => v,
            Cow::Borrowed(v) => v
        }
    }
}

pub trait Convert<T: ?Sized, E> {
    type Target: Borrow<T>;

    fn convert(&self, &E) -> Cow<Self::Target>;
}

impl<T, E> Convert<T, E> for T {
    type Target = T;

    fn convert(&self, _: &E) -> Cow<T> {
        Cow::Borrowed(self)
    }
}

pub struct BitIterator<T> {
    t: T,
    n: usize
}

impl<T: AsRef<[u64]>> BitIterator<T> {
    fn new(t: T) -> Self {
        let bits = 64 * t.as_ref().len();

        BitIterator {
            t: t,
            n: bits
        }
    }
}

impl<T: AsRef<[u64]>> Iterator for BitIterator<T> {
    type Item = bool;

    fn next(&mut self) -> Option<bool> {
        if self.n == 0 {
            None
        } else {
            self.n -= 1;
            let part = self.n / 64;
            let bit = self.n - (64 * part);

            Some(self.t.as_ref()[part] & (1 << bit) > 0)
        }
    }
}
