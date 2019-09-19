use crate::pairing::ff::{Field};
use crate::pairing::{Engine};
use std::ops::{Add, Sub, Neg};

// #[derive(Copy, Clone, Debug)]
// pub enum Variable {
//     A(usize),
//     B(usize),
//     C(usize),
// }

// impl Variable {
//     pub(crate) fn get_index(&self) -> usize {
//         match *self {
//             Variable::A(index) => index,
//             Variable::B(index) => index,
//             Variable::C(index) => index,
//         }
//     }
// }

/// Represents a variable in our constraint system.
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct Variable(pub(crate) Index);

impl Variable {
    /// This constructs a variable with an arbitrary index.
    /// Circuit implementations are not recommended to use this.
    pub fn new_unchecked(idx: Index) -> Variable {
        Variable(idx)
    }

    /// This returns the index underlying the variable.
    /// Circuit implementations are not recommended to use this.
    pub fn get_unchecked(&self) -> Index {
        self.0
    }
}

/// Represents the index of either an input variable or
/// auxillary variable.
#[derive(Copy, Clone, PartialEq, Debug, Hash, Eq)]
pub enum Index {
    Input(usize),
    Aux(usize)
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

    pub fn new(coeff: E::Fr) -> Self {  
        let mut negative_one = E::Fr::one();
        negative_one.negate();

        if coeff.is_zero() {
            Coeff::<E>::Zero
        } else if coeff == E::Fr::one() {
            Coeff::<E>::One
        } else if coeff == negative_one {
            Coeff::<E>::NegativeOne
        } else {
            Coeff::<E>::Full(coeff)
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

#[derive(Copy, Clone, Debug)]
pub struct Gate<E: Engine> {
    a_wire: Variable,
    b_wire: Variable,
    c_wire: Variable,
    pub(crate) q_l: Coeff<E>,
    pub(crate) q_r: Coeff<E>,
    pub(crate) q_o: Coeff<E>,
    pub(crate) q_m: Coeff<E>,
    pub(crate) q_c: Coeff<E>,
} 

impl<E:Engine> Gate<E> {
    pub(crate) fn empty() -> Self {
        Self {
            a_wire: Variable(Index::Aux(0)),
            b_wire: Variable(Index::Aux(0)),
            c_wire: Variable(Index::Aux(0)),
            q_l: Coeff::<E>::Zero,
            q_r: Coeff::<E>::Zero,
            q_o: Coeff::<E>::Zero,
            q_m: Coeff::<E>::Zero,
            q_c: Coeff::<E>::Zero,
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
            q_l: Coeff::<E>::Zero,
            q_r: Coeff::<E>::Zero,
            q_o: Coeff::<E>::NegativeOne,
            q_m: Coeff::<E>::One,
            q_c: Coeff::<E>::Zero,
        }
    }

    pub(crate) fn new_addition_gate(variables: (Variable, Variable, Variable)) -> Self {
        Self {
            a_wire: variables.0,
            b_wire: variables.1,
            c_wire: variables.2,
            q_l: Coeff::<E>::One,
            q_r: Coeff::<E>::One,
            q_o: Coeff::<E>::NegativeOne,
            q_m: Coeff::<E>::Zero,
            q_c: Coeff::<E>::Zero,
        }
    }

    pub(crate) fn new_lc_gate(variables: (Variable, Variable, Variable), coeffs: (E::Fr, E::Fr, E::Fr), constant: E::Fr) -> Self {
        let (a_coeff, b_coeff, c_coeff) = coeffs;
        
        Self {
            a_wire: variables.0,
            b_wire: variables.1,
            c_wire: variables.2,
            q_l: Coeff::<E>::Full(a_coeff),
            q_r: Coeff::<E>::Full(b_coeff),
            q_o: Coeff::<E>::Full(c_coeff),
            q_m: Coeff::<E>::Zero,
            q_c: Coeff::<E>::new(constant),
        }
    }

    pub(crate) fn new_enforce_zero_gate(variables: (Variable, Variable, Variable), coeffs: (E::Fr, E::Fr, E::Fr)) -> Self {
        let (a_coeff, b_coeff, c_coeff) = coeffs;
        
        Self {
            a_wire: variables.0,
            b_wire: variables.1,
            c_wire: variables.2,
            q_l: Coeff::<E>::Full(a_coeff),
            q_r: Coeff::<E>::Full(b_coeff),
            q_o: Coeff::<E>::Full(c_coeff),
            q_m: Coeff::<E>::Zero,
            q_c: Coeff::<E>::Zero,
        }
    }

    pub(crate) fn new_enforce_boolean_gate(variable: Variable, dummy_variable: Variable) -> Self {

        Self {
            a_wire: variable,
            b_wire: variable,
            c_wire: dummy_variable,
            q_l: Coeff::<E>::NegativeOne,
            q_r: Coeff::<E>::Zero,
            q_o: Coeff::<E>::Zero,
            q_m: Coeff::<E>::One,
            q_c: Coeff::<E>::Zero,
        }
    }

    pub(crate) fn new_empty_gate(dummy_variable: Variable) -> Self {

        Self {
            a_wire: dummy_variable,
            b_wire: dummy_variable,
            c_wire: dummy_variable,
            q_l: Coeff::<E>::Zero,
            q_r: Coeff::<E>::Zero,
            q_o: Coeff::<E>::Zero,
            q_m: Coeff::<E>::Zero,
            q_c: Coeff::<E>::Zero,
        }
    }

    pub(crate) fn new_enforce_constant_gate(variable: Variable, constant: Option<E::Fr>, dummy_variable: Variable) -> Self {
        let mut negative_one = E::Fr::one();
        negative_one.negate();

        let q_c = if let Some(constant) = constant {
            let mut const_negated = constant;
            const_negated.negate();
            let coeff = if const_negated.is_zero() {
                Coeff::<E>::Zero
            } else if const_negated == E::Fr::one() {
                Coeff::<E>::One
            } else if const_negated == negative_one {
                Coeff::<E>::NegativeOne
            } else {
                Coeff::<E>::Full(const_negated)
            };

            coeff
        } else {
            Coeff::<E>::Zero
        };

        Self {
            a_wire: variable,
            b_wire: dummy_variable,
            c_wire: dummy_variable,
            q_l: Coeff::<E>::One,
            q_r: Coeff::<E>::Zero,
            q_o: Coeff::<E>::Zero,
            q_m: Coeff::<E>::Zero,
            q_c: q_c,
        }
    }

    pub(crate) fn new_gate(variables: (Variable, Variable, Variable), 
        coeffs: (E::Fr, E::Fr, E::Fr, E::Fr, E::Fr)) -> Self {
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
