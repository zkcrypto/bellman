use crate::pairing::{Engine};
use crate::pairing::ff::{Field, PrimeField, BitIterator};
use crate::{SynthesisError};
use crate::cs::*;


pub trait Assignment<T> {
    fn get(&self) -> Result<&T, SynthesisError>;
}

impl<T> Assignment<T> for Option<T> {
    fn get(&self) -> Result<&T, SynthesisError> {
        match *self {
            Some(ref v) => Ok(v),
            None => Err(SynthesisError::AssignmentMissing)
        }
    }
}


/// Represents a variable in the constraint system which is guaranteed
/// to be either zero or one.
#[derive(Clone)]
pub struct AllocatedBit {
    variable: Variable,
    value: Option<bool>
}

impl AllocatedBit {
    pub fn get_value(&self) -> Option<bool> {
        self.value
    }

    pub fn get_variable(&self) -> Variable {
        self.variable
    }

    /// Allocate a variable in the constraint system which can only be a
    /// boolean value. Further, constrain that the boolean is false
    /// unless the condition is false.
    pub fn alloc_conditionally<E, CS>(
        mut cs: CS,
        value: Option<bool>,
        must_be_false: &AllocatedBit
    ) -> Result<Self, SynthesisError>
        where E: Engine,
              CS: ConstraintSystem<E>
    {
        let var = cs.alloc(|| "boolean", || {
            if *value.get()? {
                Ok(E::Fr::one())
            } else {
                Ok(E::Fr::zero())
            }
        })?;

        // Constrain: (1 - must_be_false - a) * a = 0
        // if must_be_false is true, the equation
        // reduces to -a * a = 0, which implies a = 0.
        // if must_be_false is false, the equation
        // reduces to (1 - a) * a = 0, which is a
        // traditional boolean constraint.
        cs.enforce(
            || "boolean constraint",
            |lc| lc + CS::one() - must_be_false.variable - var,
            |lc| lc + var,
            |lc| lc
        );

        Ok(AllocatedBit {
            variable: var,
            value: value
        })
    }

    /// Allocate a variable in the constraint system which can only be a
    /// boolean value.
    pub fn alloc<E, CS>(
        mut cs: CS,
        value: Option<bool>,
    ) -> Result<Self, SynthesisError>
        where E: Engine,
              CS: ConstraintSystem<E>
    {
        let var = cs.alloc(|| "boolean", || {
            if *value.get()? {
                Ok(E::Fr::one())
            } else {
                Ok(E::Fr::zero())
            }
        })?;

        // Constrain: (1 - a) * a = 0
        // This constrains a to be either 0 or 1.
        cs.enforce(
            || "boolean constraint",
            |lc| lc + CS::one() - var,
            |lc| lc + var,
            |lc| lc
        );

        Ok(AllocatedBit {
            variable: var,
            value: value
        })
    }

    /// Performs an XOR operation over the two operands, returning
    /// an `AllocatedBit`.
    pub fn xor<E, CS>(
        mut cs: CS,
        a: &Self,
        b: &Self
    ) -> Result<Self, SynthesisError>
        where E: Engine,
              CS: ConstraintSystem<E>
    {
        let mut result_value = None;

        let result_var = cs.alloc(|| "xor result", || {
            if *a.value.get()? ^ *b.value.get()? {
                result_value = Some(true);

                Ok(E::Fr::one())
            } else {
                result_value = Some(false);

                Ok(E::Fr::zero())
            }
        })?;

        // Constrain (a + a) * (b) = (a + b - c)
        // Given that a and b are boolean constrained, if they
        // are equal, the only solution for c is 0, and if they
        // are different, the only solution for c is 1.
        //
        // ¬(a ∧ b) ∧ ¬(¬a ∧ ¬b) = c
        // (1 - (a * b)) * (1 - ((1 - a) * (1 - b))) = c
        // (1 - ab) * (1 - (1 - a - b + ab)) = c
        // (1 - ab) * (a + b - ab) = c
        // a + b - ab - (a^2)b - (b^2)a + (a^2)(b^2) = c
        // a + b - ab - ab - ab + ab = c
        // a + b - 2ab = c
        // -2a * b = c - a - b
        // 2a * b = a + b - c
        // (a + a) * b = a + b - c
        cs.enforce(
            || "xor constraint",
            |lc| lc + a.variable + a.variable,
            |lc| lc + b.variable,
            |lc| lc + a.variable + b.variable - result_var
        );

        Ok(AllocatedBit {
            variable: result_var,
            value: result_value
        })
    }

    /// Performs an AND operation over the two operands, returning
    /// an `AllocatedBit`.
    pub fn and<E, CS>(
        mut cs: CS,
        a: &Self,
        b: &Self
    ) -> Result<Self, SynthesisError>
        where E: Engine,
              CS: ConstraintSystem<E>
    {
        let mut result_value = None;

        let result_var = cs.alloc(|| "and result", || {
            if *a.value.get()? & *b.value.get()? {
                result_value = Some(true);

                Ok(E::Fr::one())
            } else {
                result_value = Some(false);

                Ok(E::Fr::zero())
            }
        })?;

        // Constrain (a) * (b) = (c), ensuring c is 1 iff
        // a AND b are both 1.
        cs.enforce(
            || "and constraint",
            |lc| lc + a.variable,
            |lc| lc + b.variable,
            |lc| lc + result_var
        );

        Ok(AllocatedBit {
            variable: result_var,
            value: result_value
        })
    }

    /// Calculates `a AND (NOT b)`.
    pub fn and_not<E, CS>(
        mut cs: CS,
        a: &Self,
        b: &Self
    ) -> Result<Self, SynthesisError>
        where E: Engine,
              CS: ConstraintSystem<E>
    {
        let mut result_value = None;

        let result_var = cs.alloc(|| "and not result", || {
            if *a.value.get()? & !*b.value.get()? {
                result_value = Some(true);

                Ok(E::Fr::one())
            } else {
                result_value = Some(false);

                Ok(E::Fr::zero())
            }
        })?;

        // Constrain (a) * (1 - b) = (c), ensuring c is 1 iff
        // a is true and b is false, and otherwise c is 0.
        cs.enforce(
            || "and not constraint",
            |lc| lc + a.variable,
            |lc| lc + CS::one() - b.variable,
            |lc| lc + result_var
        );

        Ok(AllocatedBit {
            variable: result_var,
            value: result_value
        })
    }

    /// Calculates `(NOT a) AND (NOT b)`.
    pub fn nor<E, CS>(
        mut cs: CS,
        a: &Self,
        b: &Self
    ) -> Result<Self, SynthesisError>
        where E: Engine,
              CS: ConstraintSystem<E>
    {
        let mut result_value = None;

        let result_var = cs.alloc(|| "nor result", || {
            if !*a.value.get()? & !*b.value.get()? {
                result_value = Some(true);

                Ok(E::Fr::one())
            } else {
                result_value = Some(false);

                Ok(E::Fr::zero())
            }
        })?;

        // Constrain (1 - a) * (1 - b) = (c), ensuring c is 1 iff
        // a and b are both false, and otherwise c is 0.
        cs.enforce(
            || "nor constraint",
            |lc| lc + CS::one() - a.variable,
            |lc| lc + CS::one() - b.variable,
            |lc| lc + result_var
        );

        Ok(AllocatedBit {
            variable: result_var,
            value: result_value
        })
    }
}

pub fn u64_into_boolean_vec_le<E: Engine, CS: ConstraintSystem<E>>(
    mut cs: CS,
    value: Option<u64>
) -> Result<Vec<Boolean>, SynthesisError>
{
    let values = match value {
        Some(ref value) => {
            let mut tmp = Vec::with_capacity(64);

            for i in 0..64 {
                tmp.push(Some(*value >> i & 1 == 1));
            }

            tmp
        },
        None => {
            vec![None; 64]
        }
    };

    let bits = values.into_iter().enumerate().map(|(i, b)| {
        Ok(Boolean::from(AllocatedBit::alloc(
            cs.namespace(|| format!("bit {}", i)),
            b
        )?))
    }).collect::<Result<Vec<_>, SynthesisError>>()?;

    Ok(bits)
}

// changes an order of the bits to transform bits in LSB first order into
// LE bytes. Takes 8 bit chunks and reverses them
pub fn le_bits_into_le_bytes(bits: Vec<Boolean>) -> Vec<Boolean> {
    assert_eq!(bits.len() % 8, 0);

    let mut result = vec![];
    for chunk in bits.chunks(8) {
        for b in chunk.iter().rev() {
            result.push(b.clone());
        }
    }

    result
}

pub fn field_into_boolean_vec_le<E: Engine, CS: ConstraintSystem<E>, F: PrimeField>(
    cs: CS,
    value: Option<F>
) -> Result<Vec<Boolean>, SynthesisError>
{
    let v = field_into_allocated_bits_le::<E, CS, F>(cs, value)?;

    Ok(v.into_iter().map(|e| Boolean::from(e)).collect())
}

pub fn field_into_allocated_bits_le<E: Engine, CS: ConstraintSystem<E>, F: PrimeField>(
    mut cs: CS,
    value: Option<F>
) -> Result<Vec<AllocatedBit>, SynthesisError>
{
    // Deconstruct in big-endian bit order
    let values = match value {
        Some(ref value) => {
            let mut field_char = BitIterator::new(F::char());

            let mut tmp = Vec::with_capacity(F::NUM_BITS as usize);

            let mut found_one = false;
            for b in BitIterator::new(value.into_repr()) {
                // Skip leading bits
                found_one |= field_char.next().unwrap();
                if !found_one {
                    continue;
                }

                tmp.push(Some(b));
            }

            assert_eq!(tmp.len(), F::NUM_BITS as usize);

            tmp
        },
        None => {
            vec![None; F::NUM_BITS as usize]
        }
    };

    // Allocate in little-endian order
    let bits = values.into_iter().rev().enumerate().map(|(i, b)| {
        AllocatedBit::alloc(
            cs.namespace(|| format!("bit {}", i)),
            b
        )
    }).collect::<Result<Vec<_>, SynthesisError>>()?;

    Ok(bits)
}

/// This is a boolean value which may be either a constant or
/// an interpretation of an `AllocatedBit`.
#[derive(Clone)]
pub enum Boolean {
    /// Existential view of the boolean variable
    Is(AllocatedBit),
    /// Negated view of the boolean variable
    Not(AllocatedBit),
    /// Constant (not an allocated variable)
    Constant(bool)
}

impl Boolean {
    pub fn is_constant(&self) -> bool {
        match *self {
            Boolean::Constant(_) => true,
            _ => false
        }
    }

    pub fn get_variable(&self) -> Option<&AllocatedBit> {
        match *self {
            Boolean::Is(ref v) => Some(v),
            Boolean::Not(ref v) => Some(v),
            Boolean::Constant(_) => None
        }
    }

    pub fn enforce_equal<E, CS>(
        mut cs: CS,
        a: &Self,
        b: &Self
    ) -> Result<(), SynthesisError>
        where E: Engine,
              CS: ConstraintSystem<E>
    {
        match (a, b) {
            (&Boolean::Constant(a), &Boolean::Constant(b)) => {
                if a == b {
                    Ok(())
                } else {
                    Err(SynthesisError::Unsatisfiable)
                }
            },
            (&Boolean::Constant(true), a) | (a, &Boolean::Constant(true)) => {
                cs.enforce(
                    || "enforce equal to one",
                    |lc| lc,
                    |lc| lc,
                    |lc| lc + CS::one() - &a.lc(CS::one(), E::Fr::one())
                );

                Ok(())
            },
            (&Boolean::Constant(false), a) | (a, &Boolean::Constant(false)) => {
                cs.enforce(
                    || "enforce equal to zero",
                    |lc| lc,
                    |lc| lc,
                    |_| a.lc(CS::one(), E::Fr::one())
                );

                Ok(())
            },
            (a, b) => {
                cs.enforce(
                    || "enforce equal",
                    |lc| lc,
                    |lc| lc,
                    |_| a.lc(CS::one(), E::Fr::one()) - &b.lc(CS::one(), E::Fr::one())
                );

                Ok(())
            }
        }
    }

    pub fn get_value(&self) -> Option<bool> {
        match self {
            &Boolean::Constant(c) => Some(c),
            &Boolean::Is(ref v) => v.get_value(),
            &Boolean::Not(ref v) => v.get_value().map(|b| !b)
        }
    }

    pub fn lc<E: Engine>(
        &self,
        one: Variable,
        coeff: E::Fr
    ) -> LinearCombination<E>
    {
        match self {
            &Boolean::Constant(c) => {
                if c {
                    LinearCombination::<E>::zero() + (coeff, one)
                } else {
                    LinearCombination::<E>::zero()
                }
            },
            &Boolean::Is(ref v) => {
                LinearCombination::<E>::zero() + (coeff, v.get_variable())
            },
            &Boolean::Not(ref v) => {
                LinearCombination::<E>::zero() + (coeff, one) - (coeff, v.get_variable())
            }
        }
    }

    /// Construct a boolean from a known constant
    pub fn constant(b: bool) -> Self {
        Boolean::Constant(b)
    }

    /// Return a negated interpretation of this boolean.
    pub fn not(&self) -> Self {
        match self {
            &Boolean::Constant(c) => Boolean::Constant(!c),
            &Boolean::Is(ref v) => Boolean::Not(v.clone()),
            &Boolean::Not(ref v) => Boolean::Is(v.clone())
        }
    }

    /// Perform XOR over two boolean operands
    pub fn xor<'a, E, CS>(
        cs: CS,
        a: &'a Self,
        b: &'a Self
    ) -> Result<Self, SynthesisError>
        where E: Engine,
              CS: ConstraintSystem<E>
    {
        match (a, b) {
            (&Boolean::Constant(false), x) | (x, &Boolean::Constant(false)) => Ok(x.clone()),
            (&Boolean::Constant(true), x) | (x, &Boolean::Constant(true)) => Ok(x.not()),
            // a XOR (NOT b) = NOT(a XOR b)
            (is @ &Boolean::Is(_), not @ &Boolean::Not(_)) | (not @ &Boolean::Not(_), is @ &Boolean::Is(_)) => {
                Ok(Boolean::xor(
                    cs,
                    is,
                    &not.not()
                )?.not())
            },
            // a XOR b = (NOT a) XOR (NOT b)
            (&Boolean::Is(ref a), &Boolean::Is(ref b)) | (&Boolean::Not(ref a), &Boolean::Not(ref b)) => {
                Ok(Boolean::Is(AllocatedBit::xor(cs, a, b)?))
            }
        }
    }

    /// Perform AND over two boolean operands
    pub fn and<'a, E, CS>(
        cs: CS,
        a: &'a Self,
        b: &'a Self
    ) -> Result<Self, SynthesisError>
        where E: Engine,
              CS: ConstraintSystem<E>
    {
        match (a, b) {
            // false AND x is always false
            (&Boolean::Constant(false), _) | (_, &Boolean::Constant(false)) => Ok(Boolean::Constant(false)),
            // true AND x is always x
            (&Boolean::Constant(true), x) | (x, &Boolean::Constant(true)) => Ok(x.clone()),
            // a AND (NOT b)
            (&Boolean::Is(ref is), &Boolean::Not(ref not)) | (&Boolean::Not(ref not), &Boolean::Is(ref is)) => {
                Ok(Boolean::Is(AllocatedBit::and_not(cs, is, not)?))
            },
            // (NOT a) AND (NOT b) = a NOR b
            (&Boolean::Not(ref a), &Boolean::Not(ref b)) => {
                Ok(Boolean::Is(AllocatedBit::nor(cs, a, b)?))
            },
            // a AND b
            (&Boolean::Is(ref a), &Boolean::Is(ref b)) => {
                Ok(Boolean::Is(AllocatedBit::and(cs, a, b)?))
            }
        }
    }

    /// Computes (a and b) xor ((not a) and c)
    pub fn sha256_ch<'a, E, CS>(
        mut cs: CS,
        a: &'a Self,
        b: &'a Self,
        c: &'a Self
    ) -> Result<Self, SynthesisError>
        where E: Engine,
              CS: ConstraintSystem<E>
    {
        let ch_value = match (a.get_value(), b.get_value(), c.get_value()) {
            (Some(a), Some(b), Some(c)) => {
                // (a and b) xor ((not a) and c)
                Some((a & b) ^ ((!a) & c))
            },
            _ => None
        };

        match (a, b, c) {
            (&Boolean::Constant(_),
            &Boolean::Constant(_),
            &Boolean::Constant(_)) => {
                // They're all constants, so we can just compute the value.

                return Ok(Boolean::Constant(ch_value.expect("they're all constants")));
            },
            (&Boolean::Constant(false), _, c) => {
                // If a is false
                // (a and b) xor ((not a) and c)
                // equals
                // (false) xor (c)
                // equals
                // c
                return Ok(c.clone());
            },
            (a, &Boolean::Constant(false), c) => {
                // If b is false
                // (a and b) xor ((not a) and c)
                // equals
                // ((not a) and c)
                return Boolean::and(
                    cs,
                    &a.not(),
                    &c
                );
            },
            (a, b, &Boolean::Constant(false)) => {
                // If c is false
                // (a and b) xor ((not a) and c)
                // equals
                // (a and b)
                return Boolean::and(
                    cs,
                    &a,
                    &b
                );
            },
            (a, b, &Boolean::Constant(true)) => {
                // If c is true
                // (a and b) xor ((not a) and c)
                // equals
                // (a and b) xor (not a)
                // equals
                // not (a and (not b))
                return Ok(Boolean::and(
                    cs,
                    &a,
                    &b.not()
                )?.not());
            },
            (a, &Boolean::Constant(true), c) => {
                // If b is true
                // (a and b) xor ((not a) and c)
                // equals
                // a xor ((not a) and c)
                // equals
                // not ((not a) and (not c))
                return Ok(Boolean::and(
                    cs,
                    &a.not(),
                    &c.not()
                )?.not());
            },
            (&Boolean::Constant(true), _, _) => {
                // If a is true
                // (a and b) xor ((not a) and c)
                // equals
                // b xor ((not a) and c)
                // So we just continue!
            },
            (&Boolean::Is(_), &Boolean::Is(_), &Boolean::Is(_)) |
            (&Boolean::Is(_), &Boolean::Is(_), &Boolean::Not(_)) |
            (&Boolean::Is(_), &Boolean::Not(_), &Boolean::Is(_)) |
            (&Boolean::Is(_), &Boolean::Not(_), &Boolean::Not(_)) |
            (&Boolean::Not(_), &Boolean::Is(_), &Boolean::Is(_)) |
            (&Boolean::Not(_), &Boolean::Is(_), &Boolean::Not(_)) |
            (&Boolean::Not(_), &Boolean::Not(_), &Boolean::Is(_)) |
            (&Boolean::Not(_), &Boolean::Not(_), &Boolean::Not(_))
            => {}
        }

        let ch = cs.alloc(|| "ch", || {
            ch_value.get().map(|v| {
                if *v {
                    E::Fr::one()
                } else {
                    E::Fr::zero()
                }
            })
        })?;

        // a(b - c) = ch - c
        cs.enforce(
            || "ch computation",
            |_| b.lc(CS::one(), E::Fr::one())
                - &c.lc(CS::one(), E::Fr::one()),
            |_| a.lc(CS::one(), E::Fr::one()),
            |lc| lc + ch - &c.lc(CS::one(), E::Fr::one())
        );

        Ok(AllocatedBit {
            value: ch_value,
            variable: ch
        }.into())
    }

    /// Computes (a and b) xor (a and c) xor (b and c)
    pub fn sha256_maj<'a, E, CS>(
        mut cs: CS,
        a: &'a Self,
        b: &'a Self,
        c: &'a Self,
    ) -> Result<Self, SynthesisError>
        where E: Engine,
              CS: ConstraintSystem<E>
    {
        let maj_value = match (a.get_value(), b.get_value(), c.get_value()) {
            (Some(a), Some(b), Some(c)) => {
                // (a and b) xor (a and c) xor (b and c)
                Some((a & b) ^ (a & c) ^ (b & c))
            },
            _ => None
        };

        match (a, b, c) {
            (&Boolean::Constant(_),
            &Boolean::Constant(_),
            &Boolean::Constant(_)) => {
                // They're all constants, so we can just compute the value.

                return Ok(Boolean::Constant(maj_value.expect("they're all constants")));
            },
            (&Boolean::Constant(false), b, c) => {
                // If a is false,
                // (a and b) xor (a and c) xor (b and c)
                // equals
                // (b and c)
                return Boolean::and(
                    cs,
                    b,
                    c
                );
            },
            (a, &Boolean::Constant(false), c) => {
                // If b is false,
                // (a and b) xor (a and c) xor (b and c)
                // equals
                // (a and c)
                return Boolean::and(
                    cs,
                    a,
                    c
                );
            },
            (a, b, &Boolean::Constant(false)) => {
                // If c is false,
                // (a and b) xor (a and c) xor (b and c)
                // equals
                // (a and b)
                return Boolean::and(
                    cs,
                    a,
                    b
                );
            },
            (a, b, &Boolean::Constant(true)) => {
                // If c is true,
                // (a and b) xor (a and c) xor (b and c)
                // equals
                // (a and b) xor (a) xor (b)
                // equals
                // not ((not a) and (not b))
                return Ok(Boolean::and(
                    cs,
                    &a.not(),
                    &b.not()
                )?.not());
            },
            (a, &Boolean::Constant(true), c) => {
                // If b is true,
                // (a and b) xor (a and c) xor (b and c)
                // equals
                // (a) xor (a and c) xor (c)
                return Ok(Boolean::and(
                    cs,
                    &a.not(),
                    &c.not()
                )?.not());
            },
            (&Boolean::Constant(true), b, c) => {
                // If a is true,
                // (a and b) xor (a and c) xor (b and c)
                // equals
                // (b) xor (c) xor (b and c)
                return Ok(Boolean::and(
                    cs,
                    &b.not(),
                    &c.not()
                )?.not());
            },
            (&Boolean::Is(_), &Boolean::Is(_), &Boolean::Is(_)) |
            (&Boolean::Is(_), &Boolean::Is(_), &Boolean::Not(_)) |
            (&Boolean::Is(_), &Boolean::Not(_), &Boolean::Is(_)) |
            (&Boolean::Is(_), &Boolean::Not(_), &Boolean::Not(_)) |
            (&Boolean::Not(_), &Boolean::Is(_), &Boolean::Is(_)) |
            (&Boolean::Not(_), &Boolean::Is(_), &Boolean::Not(_)) |
            (&Boolean::Not(_), &Boolean::Not(_), &Boolean::Is(_)) |
            (&Boolean::Not(_), &Boolean::Not(_), &Boolean::Not(_))
            => {}
        }

        let maj = cs.alloc(|| "maj", || {
            maj_value.get().map(|v| {
                if *v {
                    E::Fr::one()
                } else {
                    E::Fr::zero()
                }
            })
        })?;

        // ¬(¬a ∧ ¬b) ∧ ¬(¬a ∧ ¬c) ∧ ¬(¬b ∧ ¬c)
        // (1 - ((1 - a) * (1 - b))) * (1 - ((1 - a) * (1 - c))) * (1 - ((1 - b) * (1 - c)))
        // (a + b - ab) * (a + c - ac) * (b + c - bc)
        // -2abc + ab + ac + bc
        // a (-2bc + b + c) + bc
        //
        // (b) * (c) = (bc)
        // (2bc - b - c) * (a) = bc - maj

        let bc = Self::and(
            cs.namespace(|| "b and c"),
            b,
            c
        )?;

        cs.enforce(
            || "maj computation",
            |_| bc.lc(CS::one(), E::Fr::one())
                + &bc.lc(CS::one(), E::Fr::one())
                - &b.lc(CS::one(), E::Fr::one())
                - &c.lc(CS::one(), E::Fr::one()),
            |_| a.lc(CS::one(), E::Fr::one()),
            |_| bc.lc(CS::one(), E::Fr::one()) - maj
        );

        Ok(AllocatedBit {
            value: maj_value,
            variable: maj
        }.into())
    }
}

impl From<AllocatedBit> for Boolean {
    fn from(b: AllocatedBit) -> Boolean {
        Boolean::Is(b)
    }
}

