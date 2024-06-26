//! Gadgets represent numbers in the scalar field of the underlying curve.

use ff::{PrimeField, PrimeFieldBits};

use crate::{ConstraintSystem, LinearCombination, SynthesisError, Variable};

use super::Assignment;

use super::boolean::{self, AllocatedBit, Boolean};

pub struct AllocatedNum<Scalar: PrimeField> {
    value: Option<Scalar>,
    variable: Variable,
}

impl<Scalar: PrimeField> Clone for AllocatedNum<Scalar> {
    fn clone(&self) -> Self {
        AllocatedNum {
            value: self.value,
            variable: self.variable,
        }
    }
}

impl<Scalar: PrimeField> AllocatedNum<Scalar> {
    pub fn alloc<CS, F>(mut cs: CS, value: F) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<Scalar>,
        F: FnOnce() -> Result<Scalar, SynthesisError>,
    {
        let mut new_value = None;
        let var = cs.alloc(
            || "num",
            || {
                let tmp = value()?;

                new_value = Some(tmp);

                Ok(tmp)
            },
        )?;

        Ok(AllocatedNum {
            value: new_value,
            variable: var,
        })
    }

    pub fn inputize<CS>(&self, mut cs: CS) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<Scalar>,
    {
        let input = cs.alloc_input(|| "input variable", || Ok(*self.value.get()?))?;

        cs.enforce(
            || "enforce input is correct",
            |lc| lc + input,
            |lc| lc + CS::one(),
            |lc| lc + self.variable,
        );

        Ok(())
    }

    /// Deconstructs this allocated number into its
    /// boolean representation in little-endian bit
    /// order, requiring that the representation
    /// strictly exists "in the field" (i.e., a
    /// congruency is not allowed.)
    pub fn to_bits_le_strict<CS>(&self, mut cs: CS) -> Result<Vec<Boolean>, SynthesisError>
    where
        Scalar: PrimeFieldBits,
        CS: ConstraintSystem<Scalar>,
    {
        pub fn kary_and<Scalar, CS>(
            mut cs: CS,
            v: &[AllocatedBit],
        ) -> Result<AllocatedBit, SynthesisError>
        where
            Scalar: PrimeField,
            CS: ConstraintSystem<Scalar>,
        {
            assert!(!v.is_empty());

            // Let's keep this simple for now and just AND them all
            // manually
            let mut cur = None;

            for (i, v) in v.iter().enumerate() {
                if cur.is_none() {
                    cur = Some(v.clone());
                } else {
                    cur = Some(AllocatedBit::and(
                        cs.namespace(|| format!("and {}", i)),
                        cur.as_ref().unwrap(),
                        v,
                    )?);
                }
            }

            Ok(cur.expect("v.len() > 0"))
        }

        // We want to ensure that the bit representation of a is
        // less than or equal to r - 1.
        let a = self.value.map(|e| e.to_le_bits());
        let b = (-Scalar::ONE).to_le_bits();

        // Get the bits of a in big-endian order
        let mut a = a.as_ref().map(|e| e.iter().by_vals().rev());

        let mut result = vec![];

        // Runs of ones in r
        let mut last_run = None;
        let mut current_run = vec![];

        let mut found_one = false;
        let mut i = 0;
        for b in b.iter().by_vals().rev() {
            let a_bit = a.as_mut().map(|e| e.next().unwrap());

            // Skip over unset bits at the beginning
            found_one |= b;
            if !found_one {
                // a_bit should also be false
                if let Some(e) = a_bit {
                    assert!(!e);
                }
                continue;
            }

            if b {
                // This is part of a run of ones. Let's just
                // allocate the boolean with the expected value.
                let a_bit = AllocatedBit::alloc(cs.namespace(|| format!("bit {}", i)), a_bit)?;
                // ... and add it to the current run of ones.
                current_run.push(a_bit.clone());
                result.push(a_bit);
            } else {
                if !current_run.is_empty() {
                    // This is the start of a run of zeros, but we need
                    // to k-ary AND against `last_run` first.

                    if last_run.is_some() {
                        current_run.push(last_run.clone().unwrap());
                    }
                    last_run = Some(kary_and(
                        cs.namespace(|| format!("run ending at {}", i)),
                        &current_run,
                    )?);
                    current_run.truncate(0);
                }

                // If `last_run` is true, `a` must be false, or it would
                // not be in the field.
                //
                // If `last_run` is false, `a` can be true or false.

                let a_bit = AllocatedBit::alloc_conditionally(
                    cs.namespace(|| format!("bit {}", i)),
                    a_bit,
                    last_run.as_ref().expect("char always starts with a one"),
                )?;
                result.push(a_bit);
            }

            i += 1;
        }

        // char is prime, so we'll always end on
        // a run of zeros.
        assert_eq!(current_run.len(), 0);

        // Now, we have `result` in big-endian order.
        // However, now we have to unpack self!

        let mut lc = LinearCombination::zero();
        let mut coeff = Scalar::ONE;

        for bit in result.iter().rev() {
            lc = lc + (coeff, bit.get_variable());

            coeff = coeff.double();
        }

        lc = lc - self.variable;

        cs.enforce(|| "unpacking constraint", |lc| lc, |lc| lc, |_| lc);

        // Convert into booleans, and reverse for little-endian bit order
        Ok(result.into_iter().map(Boolean::from).rev().collect())
    }

    /// Convert the allocated number into its little-endian representation.
    /// Note that this does not strongly enforce that the commitment is
    /// "in the field."
    pub fn to_bits_le<CS>(&self, mut cs: CS) -> Result<Vec<Boolean>, SynthesisError>
    where
        Scalar: PrimeFieldBits,
        CS: ConstraintSystem<Scalar>,
    {
        let bits = boolean::field_into_allocated_bits_le(&mut cs, self.value)?;

        let mut lc = LinearCombination::zero();
        let mut coeff = Scalar::ONE;

        for bit in bits.iter() {
            lc = lc + (coeff, bit.get_variable());

            coeff = coeff.double();
        }

        lc = lc - self.variable;

        cs.enforce(|| "unpacking constraint", |lc| lc, |lc| lc, |_| lc);

        Ok(bits.into_iter().map(Boolean::from).collect())
    }

    pub fn mul<CS>(&self, mut cs: CS, other: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<Scalar>,
    {
        let mut value = None;

        let var = cs.alloc(
            || "product num",
            || {
                let mut tmp = *self.value.get()?;
                tmp.mul_assign(other.value.get()?);

                value = Some(tmp);

                Ok(tmp)
            },
        )?;

        // Constrain: a * b = ab
        cs.enforce(
            || "multiplication constraint",
            |lc| lc + self.variable,
            |lc| lc + other.variable,
            |lc| lc + var,
        );

        Ok(AllocatedNum {
            value,
            variable: var,
        })
    }

    pub fn square<CS>(&self, mut cs: CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<Scalar>,
    {
        let mut value = None;

        let var = cs.alloc(
            || "squared num",
            || {
                let tmp = self.value.get()?.square();

                value = Some(tmp);

                Ok(tmp)
            },
        )?;

        // Constrain: a * a = aa
        cs.enforce(
            || "squaring constraint",
            |lc| lc + self.variable,
            |lc| lc + self.variable,
            |lc| lc + var,
        );

        Ok(AllocatedNum {
            value,
            variable: var,
        })
    }

    pub fn assert_nonzero<CS>(&self, mut cs: CS) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<Scalar>,
    {
        let inv = cs.alloc(
            || "ephemeral inverse",
            || {
                let tmp = *self.value.get()?;

                if tmp.is_zero_vartime() {
                    Err(SynthesisError::DivisionByZero)
                } else {
                    Ok(tmp.invert().unwrap())
                }
            },
        )?;

        // Constrain a * inv = 1, which is only valid
        // iff a has a multiplicative inverse, untrue
        // for zero.
        cs.enforce(
            || "nonzero assertion constraint",
            |lc| lc + self.variable,
            |lc| lc + inv,
            |lc| lc + CS::one(),
        );

        Ok(())
    }

    /// Takes two allocated numbers (a, b) and returns
    /// (b, a) if the condition is true, and (a, b)
    /// otherwise.
    pub fn conditionally_reverse<CS>(
        mut cs: CS,
        a: &Self,
        b: &Self,
        condition: &Boolean,
    ) -> Result<(Self, Self), SynthesisError>
    where
        CS: ConstraintSystem<Scalar>,
    {
        let c = Self::alloc(cs.namespace(|| "conditional reversal result 1"), || {
            if *condition.get_value().get()? {
                Ok(*b.value.get()?)
            } else {
                Ok(*a.value.get()?)
            }
        })?;

        cs.enforce(
            || "first conditional reversal",
            |lc| lc + a.variable - b.variable,
            |_| condition.lc(CS::one(), Scalar::ONE),
            |lc| lc + a.variable - c.variable,
        );

        let d = Self::alloc(cs.namespace(|| "conditional reversal result 2"), || {
            if *condition.get_value().get()? {
                Ok(*a.value.get()?)
            } else {
                Ok(*b.value.get()?)
            }
        })?;

        cs.enforce(
            || "second conditional reversal",
            |lc| lc + b.variable - a.variable,
            |_| condition.lc(CS::one(), Scalar::ONE),
            |lc| lc + b.variable - d.variable,
        );

        Ok((c, d))
    }

    pub fn get_value(&self) -> Option<Scalar> {
        self.value
    }

    pub fn get_variable(&self) -> Variable {
        self.variable
    }
}

pub struct Num<Scalar: PrimeField> {
    value: Option<Scalar>,
    lc: LinearCombination<Scalar>,
}

impl<Scalar: PrimeField> From<AllocatedNum<Scalar>> for Num<Scalar> {
    fn from(num: AllocatedNum<Scalar>) -> Num<Scalar> {
        Num {
            value: num.value,
            lc: LinearCombination::<Scalar>::zero() + num.variable,
        }
    }
}

impl<Scalar: PrimeField> Num<Scalar> {
    pub fn zero() -> Self {
        Num {
            value: Some(Scalar::ZERO),
            lc: LinearCombination::zero(),
        }
    }

    pub fn get_value(&self) -> Option<Scalar> {
        self.value
    }

    pub fn lc(&self, coeff: Scalar) -> LinearCombination<Scalar> {
        LinearCombination::zero() + (coeff, &self.lc)
    }

    pub fn add_bool_with_coeff(self, one: Variable, bit: &Boolean, coeff: Scalar) -> Self {
        let newval = match (self.value, bit.get_value()) {
            (Some(mut curval), Some(bval)) => {
                if bval {
                    curval.add_assign(&coeff);
                }

                Some(curval)
            }
            _ => None,
        };

        Num {
            value: newval,
            lc: self.lc + &bit.lc(one, coeff),
        }
    }
}

#[cfg(test)]
mod test {
    use crate::ConstraintSystem;
    use bls12_381::Scalar;
    use ff::{Field, PrimeField, PrimeFieldBits};
    use rand_core::SeedableRng;
    use rand_xorshift::XorShiftRng;
    use std::ops::{Neg, SubAssign};

    use super::{AllocatedNum, Boolean};
    use crate::gadgets::test::*;

    #[test]
    fn test_allocated_num() {
        let mut cs = TestConstraintSystem::new();

        AllocatedNum::alloc(&mut cs, || Ok(Scalar::ONE)).unwrap();

        assert!(cs.get("num") == Scalar::ONE);
    }

    #[test]
    fn test_num_squaring() {
        let mut cs = TestConstraintSystem::new();

        let n = AllocatedNum::alloc(&mut cs, || Ok(Scalar::from(3))).unwrap();
        let n2 = n.square(&mut cs).unwrap();

        assert!(cs.is_satisfied());
        assert!(cs.get("squared num") == Scalar::from(9));
        assert!(n2.value.unwrap() == Scalar::from(9));
        cs.set("squared num", Scalar::from(10));
        assert!(!cs.is_satisfied());
    }

    #[test]
    fn test_num_multiplication() {
        let mut cs = TestConstraintSystem::new();

        let n = AllocatedNum::alloc(cs.namespace(|| "a"), || Ok(Scalar::from(12))).unwrap();
        let n2 = AllocatedNum::alloc(cs.namespace(|| "b"), || Ok(Scalar::from(10))).unwrap();
        let n3 = n.mul(&mut cs, &n2).unwrap();

        assert!(cs.is_satisfied());
        assert!(cs.get("product num") == Scalar::from(120));
        assert!(n3.value.unwrap() == Scalar::from(120));
        cs.set("product num", Scalar::from(121));
        assert!(!cs.is_satisfied());
    }

    #[test]
    fn test_num_conditional_reversal() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x3d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);
        {
            let mut cs = TestConstraintSystem::new();

            let a =
                AllocatedNum::alloc(cs.namespace(|| "a"), || Ok(Scalar::random(&mut rng))).unwrap();
            let b =
                AllocatedNum::alloc(cs.namespace(|| "b"), || Ok(Scalar::random(&mut rng))).unwrap();
            let condition = Boolean::constant(false);
            let (c, d) = AllocatedNum::conditionally_reverse(&mut cs, &a, &b, &condition).unwrap();

            assert!(cs.is_satisfied());

            assert_eq!(a.value.unwrap(), c.value.unwrap());
            assert_eq!(b.value.unwrap(), d.value.unwrap());
        }

        {
            let mut cs = TestConstraintSystem::new();

            let a =
                AllocatedNum::alloc(cs.namespace(|| "a"), || Ok(Scalar::random(&mut rng))).unwrap();
            let b =
                AllocatedNum::alloc(cs.namespace(|| "b"), || Ok(Scalar::random(&mut rng))).unwrap();
            let condition = Boolean::constant(true);
            let (c, d) = AllocatedNum::conditionally_reverse(&mut cs, &a, &b, &condition).unwrap();

            assert!(cs.is_satisfied());

            assert_eq!(a.value.unwrap(), d.value.unwrap());
            assert_eq!(b.value.unwrap(), c.value.unwrap());
        }
    }

    #[test]
    fn test_num_nonzero() {
        {
            let mut cs = TestConstraintSystem::new();

            let n = AllocatedNum::alloc(&mut cs, || Ok(Scalar::from(3))).unwrap();
            n.assert_nonzero(&mut cs).unwrap();

            assert!(cs.is_satisfied());
            cs.set("ephemeral inverse", Scalar::from(3));
            assert!(cs.which_is_unsatisfied() == Some("nonzero assertion constraint"));
        }
        {
            let mut cs = TestConstraintSystem::new();

            let n = AllocatedNum::alloc(&mut cs, || Ok(Scalar::ZERO)).unwrap();
            assert!(n.assert_nonzero(&mut cs).is_err());
        }
    }

    #[test]
    fn test_into_bits_strict() {
        let negone = Scalar::ONE.neg();

        let mut cs = TestConstraintSystem::new();

        let n = AllocatedNum::alloc(&mut cs, || Ok(negone)).unwrap();
        n.to_bits_le_strict(&mut cs).unwrap();

        assert!(cs.is_satisfied());

        // make the bit representation the characteristic
        cs.set("bit 254/boolean", Scalar::ONE);

        // this makes the conditional boolean constraint fail
        assert_eq!(
            cs.which_is_unsatisfied().unwrap(),
            "bit 254/boolean constraint"
        );
    }

    #[test]
    fn test_into_bits() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x3d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for i in 0..200 {
            let r = Scalar::random(&mut rng);
            let mut cs = TestConstraintSystem::new();

            let n = AllocatedNum::alloc(&mut cs, || Ok(r)).unwrap();

            let bits = if i % 2 == 0 {
                n.to_bits_le(&mut cs).unwrap()
            } else {
                n.to_bits_le_strict(&mut cs).unwrap()
            };

            assert!(cs.is_satisfied());

            for (b, a) in r
                .to_le_bits()
                .iter()
                .by_vals()
                .rev()
                .skip(1)
                .zip(bits.iter().rev())
            {
                if let Boolean::Is(ref a) = a {
                    assert_eq!(b, a.get_value().unwrap());
                } else {
                    unreachable!()
                }
            }

            cs.set("num", Scalar::random(&mut rng));
            assert!(!cs.is_satisfied());
            cs.set("num", r);
            assert!(cs.is_satisfied());

            for i in 0..Scalar::NUM_BITS {
                let name = format!("bit {}/boolean", i);
                let cur = cs.get(&name);
                let mut tmp = Scalar::ONE;
                tmp.sub_assign(&cur);
                cs.set(&name, tmp);
                assert!(!cs.is_satisfied());
                cs.set(&name, cur);
                assert!(cs.is_satisfied());
            }
        }
    }
}
