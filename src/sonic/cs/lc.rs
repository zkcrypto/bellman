use crate::pairing::ff::{Field};
use crate::pairing::{Engine};
use std::ops::{Add, Sub, Neg};

/// This represents a linear combination of some variables, with coefficients
/// in the scalar field of a pairing-friendly elliptic curve group.
#[derive(Clone)]
pub struct LinearCombination<E: Engine>(Vec<(Variable, Coeff<E>)>);

impl<E: Engine> From<Variable> for LinearCombination<E> {
    fn from(var: Variable) -> LinearCombination<E> {
        LinearCombination::<E>::zero() + var
    }
}

impl<E: Engine> AsRef<[(Variable, Coeff<E>)]> for LinearCombination<E> {
    fn as_ref(&self) -> &[(Variable, Coeff<E>)] {
        &self.0
    }
}

impl<E: Engine> LinearCombination<E> {
    pub fn zero() -> LinearCombination<E> {
        LinearCombination(vec![])
    }
}

impl<E: Engine> Add<(Coeff<E>, Variable)> for LinearCombination<E> {
    type Output = LinearCombination<E>;

    fn add(mut self, (coeff, var): (Coeff<E>, Variable)) -> LinearCombination<E> {
        self.0.push((var, coeff));

        self
    }
}

impl<E: Engine> Sub<(Coeff<E>, Variable)> for LinearCombination<E> {
    type Output = LinearCombination<E>;

    fn sub(self, (coeff, var): (Coeff<E>, Variable)) -> LinearCombination<E> {
        self + (-coeff, var)
    }
}

impl<E: Engine> Add<Variable> for LinearCombination<E> {
    type Output = LinearCombination<E>;

    fn add(self, other: Variable) -> LinearCombination<E> {
        self + (Coeff::One, other)
    }
}

impl<E: Engine> Sub<Variable> for LinearCombination<E> {
    type Output = LinearCombination<E>;

    fn sub(self, other: Variable) -> LinearCombination<E> {
        self - (Coeff::One, other)
    }
}

impl<'a, E: Engine> Add<&'a LinearCombination<E>> for LinearCombination<E> {
    type Output = LinearCombination<E>;

    fn add(mut self, other: &'a LinearCombination<E>) -> LinearCombination<E> {
        for s in &other.0 {
            self = self + (s.1, s.0);
        }

        self
    }
}

impl<'a, E: Engine> Sub<&'a LinearCombination<E>> for LinearCombination<E> {
    type Output = LinearCombination<E>;

    fn sub(mut self, other: &'a LinearCombination<E>) -> LinearCombination<E> {
        for s in &other.0 {
            self = self - (s.1, s.0);
        }

        self
    }
}

#[derive(Copy, Clone, Debug)]
pub enum Variable {
    A(usize),
    B(usize),
    C(usize),
}

impl Variable {
    pub(crate) fn get_index(&self) -> usize {
        match *self {
            Variable::A(index) => index,
            Variable::B(index) => index,
            Variable::C(index) => index,
        }
    }
}

#[derive(Debug)]
pub enum Coeff<E: Engine> {
    Zero,
    One,
    NegativeOne,
    Full(E::Fr),
}

impl<E: Engine> Coeff<E> {
    pub fn multiply(&self, with: &mut E::Fr) {
        match self {
            Coeff::Zero => {
                *with = E::Fr::zero();
            },
            Coeff::One => {},
            Coeff::NegativeOne => {
                with.negate();
            },
            Coeff::Full(val) => {
                with.mul_assign(val);
            }
        }
    }
}

impl<E: Engine> Copy for Coeff<E> {}
impl<E: Engine> Clone for Coeff<E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<E: Engine> Neg for Coeff<E> {
    type Output = Coeff<E>;

    fn neg(self) -> Self {
        match self {
            Coeff::Zero => Coeff::Zero,
            Coeff::One => Coeff::NegativeOne,
            Coeff::NegativeOne => Coeff::One,
            Coeff::Full(mut a) => {
                a.negate();
                Coeff::Full(a)
            }
        }
    }
}