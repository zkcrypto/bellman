use crate::pairing::ff::{Field, PrimeField};
use crate::pairing::{Engine};
use std::ops::{Add, Sub, Neg};
pub use crate::plonk::cs::variable::*;

pub enum Coeff<F: PrimeField> {
    Zero,
    One,
    NegativeOne,
    Full(F),
}

impl<F: PrimeField> std::fmt::Debug for Coeff<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Coeff::Zero => {
                write!(f, "Coeff 0x0")
            },
            Coeff::One => {
                write!(f, "Coeff 0x1")
            },
            Coeff::NegativeOne => {
                write!(f, "Coeff -0x1")
            },
            Coeff::Full(c) => {
                write!(f, "Coeff {:?}", c)
            },
        }
    }
}

impl<F: PrimeField> Coeff<F> {
    pub fn multiply(&self, with: &mut F) {
        match self {
            Coeff::Zero => {
                *with = F::zero();
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

    pub fn new(coeff: F) -> Self {  
        let mut negative_one = F::one();
        negative_one.negate();

        if coeff.is_zero() {
            Coeff::<F>::Zero
        } else if coeff == F::one() {
            Coeff::<F>::One
        } else if coeff == negative_one {
            Coeff::<F>::NegativeOne
        } else {
            Coeff::<F>::Full(coeff)
        }
    }
}

impl<F: PrimeField> Copy for Coeff<F> {}
impl<F: PrimeField> Clone for Coeff<F> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<F: PrimeField> Neg for Coeff<F> {
    type Output = Coeff<F>;

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

#[derive(Copy, Clone, Debug)]
pub struct Gate<F: PrimeField> {
    variables: [Variable; 3],
    coefficients: [Coeff<F>; 6],
}

impl<F: PrimeField> Gate<F> {
    pub(crate) fn empty() -> Self {
        Self {
            variables: [Variable(Index::Aux(0)), Variable(Index::Aux(0)), Variable(Index::Aux(0))],
            coefficients: [Coeff::<F>::Zero, Coeff::<F>::Zero, Coeff::<F>::Zero, Coeff::<F>::Zero, 
                Coeff::<F>::Zero, Coeff::<F>::Zero]
        }
    }

    pub(crate) fn a_wire(&self) -> &Variable {
        &self.variables[0]
    }

    pub(crate) fn b_wire(&self) -> &Variable {
        &self.variables[1]
    }

    pub(crate) fn c_wire(&self) -> &Variable {
        &self.variables[2]
    }

    pub(crate) fn q_l(&self) -> &Coeff<F> {
        &self.coefficients[0]
    }

    pub(crate) fn q_r(&self) -> &Coeff<F> {
        &self.coefficients[1]
    }

    pub(crate) fn q_o(&self) -> &Coeff<F> {
        &self.coefficients[2]
    }

    pub(crate) fn q_m(&self) -> &Coeff<F> {
        &self.coefficients[3]
    }

    pub(crate) fn q_c(&self) -> &Coeff<F> {
        &self.coefficients[4]
    }

    //short from additional selector
    pub(crate) fn q_add_sel(&self) -> &Coeff<F> {
        &self.coefficients[5]
    }

    pub(crate) fn new_gate(variables: (Variable, Variable, Variable), 
        coeffs: (F, F, F, F, F, F)) -> Self {
        let (q_l, q_r, q_o, q_m, q_c, q_o_next) = coeffs;

        Self {
            variables: [variables.0, variables.1, variables.2],
            coefficients: [Coeff::new(q_l), Coeff::new(q_r), Coeff::new(q_o), Coeff::new(q_m), 
                Coeff::new(q_c),  Coeff::new(q_o_next)]
        }
    }

    pub(crate) fn new_enforce_constant_gate(variable: Variable, constant: Option<F>, dummy_variable: Variable) -> Self {
        let mut negative_one = F::one();
        negative_one.negate();

        let q_c = if let Some(constant) = constant {
            let mut const_negated = constant;
            const_negated.negate();
            let coeff = if const_negated.is_zero() {
                Coeff::<F>::Zero
            } else if const_negated == F::one() {
                Coeff::<F>::One
            } else if const_negated == negative_one {
                Coeff::<F>::NegativeOne
            } else {
                Coeff::<F>::Full(const_negated)
            };

            coeff
        } else {
            Coeff::<F>::Zero
        };

        Self {
            variables: [variable, dummy_variable, dummy_variable], 
            coefficients: [Coeff::<F>::One, Coeff::<F>::Zero, Coeff::<F>::Zero, Coeff::<F>::Zero, q_c, Coeff::<F>::Zero],
        }
    }

    //used omly to pad the size of constraint system to the next power of 2
    pub(crate) fn new_empty_gate(dummy_variable: Variable) -> Self {
        Self {
            variables: [dummy_variable, dummy_variable, dummy_variable],
            coefficients: [Coeff::<F>::Zero, Coeff::<F>::Zero, Coeff::<F>::Zero, Coeff::<F>::Zero,
                Coeff::<F>::Zero, Coeff::<F>::Zero]
        }
    }
}