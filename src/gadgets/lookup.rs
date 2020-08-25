//! Window table lookup gadgets.

use ff::PrimeField;

use super::boolean::Boolean;
use super::num::{AllocatedNum, Num};
use super::*;
use crate::ConstraintSystem;

// Synthesize the constants for each base pattern.
fn synth<'a, Scalar: PrimeField, I>(window_size: usize, constants: I, assignment: &mut [Scalar])
where
    I: IntoIterator<Item = &'a Scalar>,
{
    assert_eq!(assignment.len(), 1 << window_size);

    for (i, constant) in constants.into_iter().enumerate() {
        let mut cur = assignment[i].neg();
        cur.add_assign(constant);
        assignment[i] = cur;
        for (j, eval) in assignment.iter_mut().enumerate().skip(i + 1) {
            if j & i == i {
                eval.add_assign(&cur);
            }
        }
    }
}

/// Performs a 3-bit window table lookup. `bits` is in
/// little-endian order.
pub fn lookup3_xy<Scalar: PrimeField, CS>(
    mut cs: CS,
    bits: &[Boolean],
    coords: &[(Scalar, Scalar)],
) -> Result<(AllocatedNum<Scalar>, AllocatedNum<Scalar>), SynthesisError>
where
    CS: ConstraintSystem<Scalar>,
{
    assert_eq!(bits.len(), 3);
    assert_eq!(coords.len(), 8);

    // Calculate the index into `coords`
    let i = match (
        bits[0].get_value(),
        bits[1].get_value(),
        bits[2].get_value(),
    ) {
        (Some(a_value), Some(b_value), Some(c_value)) => {
            let mut tmp = 0;
            if a_value {
                tmp += 1;
            }
            if b_value {
                tmp += 2;
            }
            if c_value {
                tmp += 4;
            }
            Some(tmp)
        }
        _ => None,
    };

    // Allocate the x-coordinate resulting from the lookup
    let res_x = AllocatedNum::alloc(cs.namespace(|| "x"), || Ok(coords[*i.get()?].0))?;

    // Allocate the y-coordinate resulting from the lookup
    let res_y = AllocatedNum::alloc(cs.namespace(|| "y"), || Ok(coords[*i.get()?].1))?;

    // Compute the coefficients for the lookup constraints
    let mut x_coeffs = [Scalar::zero(); 8];
    let mut y_coeffs = [Scalar::zero(); 8];
    synth::<Scalar, _>(3, coords.iter().map(|c| &c.0), &mut x_coeffs);
    synth::<Scalar, _>(3, coords.iter().map(|c| &c.1), &mut y_coeffs);

    let precomp = Boolean::and(cs.namespace(|| "precomp"), &bits[1], &bits[2])?;

    let one = CS::one();

    cs.enforce(
        || "x-coordinate lookup",
        |lc| {
            lc + (x_coeffs[0b001], one)
                + &bits[1].lc::<Scalar>(one, x_coeffs[0b011])
                + &bits[2].lc::<Scalar>(one, x_coeffs[0b101])
                + &precomp.lc::<Scalar>(one, x_coeffs[0b111])
        },
        |lc| lc + &bits[0].lc::<Scalar>(one, Scalar::one()),
        |lc| {
            lc + res_x.get_variable()
                - (x_coeffs[0b000], one)
                - &bits[1].lc::<Scalar>(one, x_coeffs[0b010])
                - &bits[2].lc::<Scalar>(one, x_coeffs[0b100])
                - &precomp.lc::<Scalar>(one, x_coeffs[0b110])
        },
    );

    cs.enforce(
        || "y-coordinate lookup",
        |lc| {
            lc + (y_coeffs[0b001], one)
                + &bits[1].lc::<Scalar>(one, y_coeffs[0b011])
                + &bits[2].lc::<Scalar>(one, y_coeffs[0b101])
                + &precomp.lc::<Scalar>(one, y_coeffs[0b111])
        },
        |lc| lc + &bits[0].lc::<Scalar>(one, Scalar::one()),
        |lc| {
            lc + res_y.get_variable()
                - (y_coeffs[0b000], one)
                - &bits[1].lc::<Scalar>(one, y_coeffs[0b010])
                - &bits[2].lc::<Scalar>(one, y_coeffs[0b100])
                - &precomp.lc::<Scalar>(one, y_coeffs[0b110])
        },
    );

    Ok((res_x, res_y))
}

/// Performs a 3-bit window table lookup, where
/// one of the bits is a sign bit.
pub fn lookup3_xy_with_conditional_negation<Scalar: PrimeField, CS>(
    mut cs: CS,
    bits: &[Boolean],
    coords: &[(Scalar, Scalar)],
) -> Result<(Num<Scalar>, Num<Scalar>), SynthesisError>
where
    CS: ConstraintSystem<Scalar>,
{
    assert_eq!(bits.len(), 3);
    assert_eq!(coords.len(), 4);

    // Calculate the index into `coords`
    let i = match (bits[0].get_value(), bits[1].get_value()) {
        (Some(a_value), Some(b_value)) => {
            let mut tmp = 0;
            if a_value {
                tmp += 1;
            }
            if b_value {
                tmp += 2;
            }
            Some(tmp)
        }
        _ => None,
    };

    // Allocate the y-coordinate resulting from the lookup
    // and conditional negation
    let y = AllocatedNum::alloc(cs.namespace(|| "y"), || {
        let mut tmp = coords[*i.get()?].1;
        if *bits[2].get_value().get()? {
            tmp = tmp.neg();
        }
        Ok(tmp)
    })?;

    let one = CS::one();

    // Compute the coefficients for the lookup constraints
    let mut x_coeffs = [Scalar::zero(); 4];
    let mut y_coeffs = [Scalar::zero(); 4];
    synth::<Scalar, _>(2, coords.iter().map(|c| &c.0), &mut x_coeffs);
    synth::<Scalar, _>(2, coords.iter().map(|c| &c.1), &mut y_coeffs);

    let precomp = Boolean::and(cs.namespace(|| "precomp"), &bits[0], &bits[1])?;

    let x = Num::zero()
        .add_bool_with_coeff(one, &Boolean::constant(true), x_coeffs[0b00])
        .add_bool_with_coeff(one, &bits[0], x_coeffs[0b01])
        .add_bool_with_coeff(one, &bits[1], x_coeffs[0b10])
        .add_bool_with_coeff(one, &precomp, x_coeffs[0b11]);

    let y_lc = precomp.lc::<Scalar>(one, y_coeffs[0b11])
        + &bits[1].lc::<Scalar>(one, y_coeffs[0b10])
        + &bits[0].lc::<Scalar>(one, y_coeffs[0b01])
        + (y_coeffs[0b00], one);

    cs.enforce(
        || "y-coordinate lookup",
        |lc| lc + &y_lc + &y_lc,
        |lc| lc + &bits[2].lc::<Scalar>(one, Scalar::one()),
        |lc| lc + &y_lc - y.get_variable(),
    );

    Ok((x, y.into()))
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::gadgets::boolean::{AllocatedBit, Boolean};
    use crate::gadgets::test::*;

    use bls12_381::Scalar;
    use ff::Field;
    use rand_core::{RngCore, SeedableRng};
    use rand_xorshift::XorShiftRng;
    use std::ops::{AddAssign, Neg};

    #[test]
    fn test_lookup3_xy() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x3d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..100 {
            let mut cs = TestConstraintSystem::new();

            let a_val = rng.next_u32() % 2 != 0;
            let a = Boolean::from(AllocatedBit::alloc(cs.namespace(|| "a"), Some(a_val)).unwrap());

            let b_val = rng.next_u32() % 2 != 0;
            let b = Boolean::from(AllocatedBit::alloc(cs.namespace(|| "b"), Some(b_val)).unwrap());

            let c_val = rng.next_u32() % 2 != 0;
            let c = Boolean::from(AllocatedBit::alloc(cs.namespace(|| "c"), Some(c_val)).unwrap());

            let bits = vec![a, b, c];

            let points: Vec<(Scalar, Scalar)> = (0..8)
                .map(|_| (Scalar::random(&mut rng), Scalar::random(&mut rng)))
                .collect();

            let res = lookup3_xy(&mut cs, &bits, &points).unwrap();

            assert!(cs.is_satisfied());

            let mut index = 0;
            if a_val {
                index += 1
            }
            if b_val {
                index += 2
            }
            if c_val {
                index += 4
            }

            assert_eq!(res.0.get_value().unwrap(), points[index].0);
            assert_eq!(res.1.get_value().unwrap(), points[index].1);
        }
    }

    #[test]
    fn test_lookup3_xy_with_conditional_negation() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x3d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..100 {
            let mut cs = TestConstraintSystem::new();

            let a_val = rng.next_u32() % 2 != 0;
            let a = Boolean::from(AllocatedBit::alloc(cs.namespace(|| "a"), Some(a_val)).unwrap());

            let b_val = rng.next_u32() % 2 != 0;
            let b = Boolean::from(AllocatedBit::alloc(cs.namespace(|| "b"), Some(b_val)).unwrap());

            let c_val = rng.next_u32() % 2 != 0;
            let c = Boolean::from(AllocatedBit::alloc(cs.namespace(|| "c"), Some(c_val)).unwrap());

            let bits = vec![a, b, c];

            let points: Vec<(Scalar, Scalar)> = (0..4)
                .map(|_| (Scalar::random(&mut rng), Scalar::random(&mut rng)))
                .collect();

            let res = lookup3_xy_with_conditional_negation(&mut cs, &bits, &points).unwrap();

            assert!(cs.is_satisfied());

            let mut index = 0;
            if a_val {
                index += 1
            }
            if b_val {
                index += 2
            }

            assert_eq!(res.0.get_value().unwrap(), points[index].0);
            let mut tmp = points[index].1;
            if c_val {
                tmp = tmp.neg()
            }
            assert_eq!(res.1.get_value().unwrap(), tmp);
        }
    }

    #[test]
    fn test_synth() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x3d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let window_size = 4;

        let mut assignment = vec![Scalar::zero(); 1 << window_size];
        let constants: Vec<_> = (0..(1 << window_size))
            .map(|_| Scalar::random(&mut rng))
            .collect();

        synth(window_size, &constants, &mut assignment);

        for b in 0..(1 << window_size) {
            let mut acc = Scalar::zero();

            for j in 0..(1 << window_size) {
                if j & b == j {
                    acc.add_assign(&assignment[j]);
                }
            }

            assert_eq!(acc, constants[b]);
        }
    }
}
