#![feature(i128_type)]

extern crate rand;
extern crate num_cpus;
extern crate crossbeam;
extern crate byteorder;
extern crate serde;

pub mod curves;
pub mod groth;

use std::collections::HashMap;
use std::ops;

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
    type WitnessMap: Witness<E>;

    /// Synthesize the circuit into a rank-1 quadratic constraint system
    #[must_use]
    fn synthesize<CS: ConstraintSystem<E>>(self, engine: &E, cs: &mut CS) -> Self::WitnessMap;
}

pub trait Witness<E: Engine> {
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
