use crate::pairing::ff::{Field, PrimeField};
use crate::pairing::{Engine};
use std::ops::{Add, Sub, Neg};

pub use super::variable::{Variable, Index};

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

#[derive(Copy, Clone)]
pub struct Gate<F: PrimeField> {
    a_wire: Variable,
    b_wire: Variable,
    c_wire: Variable,
    pub(crate) q_l: Coeff<F>,
    pub(crate) q_r: Coeff<F>,
    pub(crate) q_o: Coeff<F>,
    pub(crate) q_m: Coeff<F>,
    pub(crate) q_c: Coeff<F>,
} 

impl<F: PrimeField> std::fmt::Debug for Gate<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Gate A = {:?}, B = {:?}, C = {:?}, q_l = {:?}, q_r = {:?}, q_o = {:?}, q_m = {:?}, q_c = {:?}", 
        self.a_wire, self.b_wire, self.c_wire, self.q_l, self.q_r, self.q_o, self.q_m, self.q_c)

    }
}

impl<F: PrimeField> Gate<F> {
    pub(crate) fn empty() -> Self {
        Self {
            a_wire: Variable(Index::Aux(0)),
            b_wire: Variable(Index::Aux(0)),
            c_wire: Variable(Index::Aux(0)),
            q_l: Coeff::<F>::Zero,
            q_r: Coeff::<F>::Zero,
            q_o: Coeff::<F>::Zero,
            q_m: Coeff::<F>::Zero,
            q_c: Coeff::<F>::Zero,
        }
    }

    pub(crate) fn a_wire(&self) -> &Variable {
        &self.a_wire
    }

    pub(crate) fn b_wire(&self) -> &Variable {
        &self.b_wire
    }

    pub(crate) fn c_wire(&self) -> &Variable {
        &self.c_wire
    }

    pub(crate) fn new_multiplication_gate(variables: (Variable, Variable, Variable)) -> Self {
        
        Self {
            a_wire: variables.0,
            b_wire: variables.1,
            c_wire: variables.2,
            q_l: Coeff::<F>::Zero,
            q_r: Coeff::<F>::Zero,
            q_o: Coeff::<F>::NegativeOne,
            q_m: Coeff::<F>::One,
            q_c: Coeff::<F>::Zero,
        }
    }

    pub(crate) fn new_addition_gate(variables: (Variable, Variable, Variable)) -> Self {
        Self {
            a_wire: variables.0,
            b_wire: variables.1,
            c_wire: variables.2,
            q_l: Coeff::<F>::One,
            q_r: Coeff::<F>::One,
            q_o: Coeff::<F>::NegativeOne,
            q_m: Coeff::<F>::Zero,
            q_c: Coeff::<F>::Zero,
        }
    }

    pub(crate) fn new_lc_gate(variables: (Variable, Variable, Variable), coeffs: (F, F, F), constant: F) -> Self {
        let (a_coeff, b_coeff, c_coeff) = coeffs;
        
        Self {
            a_wire: variables.0,
            b_wire: variables.1,
            c_wire: variables.2,
            q_l: Coeff::<F>::Full(a_coeff),
            q_r: Coeff::<F>::Full(b_coeff),
            q_o: Coeff::<F>::Full(c_coeff),
            q_m: Coeff::<F>::Zero,
            q_c: Coeff::<F>::new(constant),
        }
    }

    pub(crate) fn new_enforce_zero_gate(variables: (Variable, Variable, Variable), coeffs: (F, F, F)) -> Self {
        let (a_coeff, b_coeff, c_coeff) = coeffs;
        
        Self {
            a_wire: variables.0,
            b_wire: variables.1,
            c_wire: variables.2,
            q_l: Coeff::<F>::Full(a_coeff),
            q_r: Coeff::<F>::Full(b_coeff),
            q_o: Coeff::<F>::Full(c_coeff),
            q_m: Coeff::<F>::Zero,
            q_c: Coeff::<F>::Zero,
        }
    }

    pub(crate) fn new_enforce_boolean_gate(variable: Variable, dummy_variable: Variable) -> Self {

        Self {
            a_wire: variable,
            b_wire: variable,
            c_wire: dummy_variable,
            q_l: Coeff::<F>::NegativeOne,
            q_r: Coeff::<F>::Zero,
            q_o: Coeff::<F>::Zero,
            q_m: Coeff::<F>::One,
            q_c: Coeff::<F>::Zero,
        }
    }

    pub(crate) fn new_empty_gate(dummy_variable: Variable) -> Self {

        Self {
            a_wire: dummy_variable,
            b_wire: dummy_variable,
            c_wire: dummy_variable,
            q_l: Coeff::<F>::Zero,
            q_r: Coeff::<F>::Zero,
            q_o: Coeff::<F>::Zero,
            q_m: Coeff::<F>::Zero,
            q_c: Coeff::<F>::Zero,
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
            a_wire: variable,
            b_wire: dummy_variable,
            c_wire: dummy_variable,
            q_l: Coeff::<F>::One,
            q_r: Coeff::<F>::Zero,
            q_o: Coeff::<F>::Zero,
            q_m: Coeff::<F>::Zero,
            q_c: q_c,
        }
    }

    pub(crate) fn new_gate(variables: (Variable, Variable, Variable), 
        coeffs: (F, F, F, F, F)) -> Self {
        let (q_l, q_r, q_o, q_m, q_c) = coeffs;

        Self {
            a_wire: variables.0,
            b_wire: variables.1,
            c_wire: variables.2,
            q_l: Coeff::new(q_l),
            q_r: Coeff::new(q_r),
            q_o: Coeff::new(q_o),
            q_m: Coeff::new(q_m),
            q_c: Coeff::new(q_c),
        }
    }
}
