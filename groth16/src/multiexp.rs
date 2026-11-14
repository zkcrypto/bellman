//! Variable-time multiexponentiation over public scalars.
//!
//! Every function here is variable-time in its scalars. Callers must only pass public
//! values, or values that are unpredictable to an adversary until they are no longer
//! secret, such as batch-verification weights.

use ff::PrimeField;
use group::Group;

/// Returns the width-4 NAF digits of a little-endian integer, least significant first,
/// without trailing zeros.
fn wnaf(bytes: &[u8]) -> Vec<i8> {
    let bit = |i: usize| bytes.get(i / 8).map_or(0, |byte| (byte >> (i % 8)) & 1);
    let mut digits = Vec::with_capacity(8 * bytes.len() + 4);
    let mut carry = 0;
    let mut i = 0;
    // The position after the last byte absorbs a final carry.
    while i <= 8 * bytes.len() {
        let window = carry + (0..4).map(|k| bit(i + k) << k).sum::<u8>();
        if window % 2 == 0 {
            digits.push(0);
            i += 1;
        } else {
            // Every nonzero digit is odd, in -7..=7, and followed by three zeros.
            let digit = i8::try_from(window).expect("windows are at most 16");
            let digit = if window < 8 {
                carry = 0;
                digit
            } else {
                carry = 1;
                digit - 16
            };
            digits.extend([digit, 0, 0, 0]);
            i += 4;
        }
    }
    while digits.last() == Some(&0) {
        digits.pop();
    }
    digits
}

/// Returns whether `to_repr()` encodes scalars as little-endian integers.
///
/// Fields too small to represent the 64-bit probe value return `false`, so they use the
/// group's own multiplication.
fn is_little_endian<F: PrimeField>() -> bool {
    let probe = F::from(0x0807_0605_0403_0201).to_repr();
    let probe = probe.as_ref();
    probe.starts_with(&[1, 2, 3, 4, 5, 6, 7, 8]) && probe[8..].iter().all(|&byte| byte == 0)
}

/// Computes `sum(bases[i] * scalars[i])` in variable time.
///
/// Little-endian scalar encodings use interleaved wNAF, so all terms share one sequence
/// of doublings. Other encodings use the group's own multiplication.
pub(crate) fn multiexp_vartime<G: Group>(bases: &[G], scalars: &[G::Scalar]) -> G {
    if !is_little_endian::<G::Scalar>() {
        return bases
            .iter()
            .zip(scalars)
            .map(|(base, scalar)| *base * scalar)
            .sum();
    }

    // Odd multiples of each base, from one to seven times.
    let tables = bases
        .iter()
        .map(|&base| {
            let double = base.double();
            let mut table = [base; 4];
            for i in 1..4 {
                table[i] = table[i - 1] + double;
            }
            table
        })
        .collect::<Vec<_>>();
    let digits = scalars
        .iter()
        .map(|scalar| wnaf(scalar.to_repr().as_ref()))
        .collect::<Vec<_>>();

    let mut sum = G::identity();
    for i in (0..digits.iter().map(Vec::len).max().unwrap_or(0)).rev() {
        sum = sum.double();
        for (table, digits) in tables.iter().zip(&digits) {
            let digit = digits.get(i).copied().unwrap_or(0);
            let term = &table[usize::from(digit.unsigned_abs() / 2)];
            match digit.signum() {
                1 => sum += term,
                -1 => sum -= term,
                _ => {}
            }
        }
    }
    sum
}

#[cfg(test)]
mod tests {
    use ff::Field;

    use super::*;

    #[test]
    fn multiexp_vartime_matches_multiplication() {
        use bls12_381::{G1Projective, Scalar};
        use group::Group;
        use rand::{SeedableRng, rngs::StdRng};

        let mut rng = StdRng::seed_from_u64(0);
        // Scalars whose wNAF digits carry into higher windows, then random scalars.
        let mut scalars = vec![
            Scalar::ZERO,
            Scalar::ONE,
            -Scalar::ONE,
            Scalar::from(7),
            Scalar::from(9),
            Scalar::from(15),
            Scalar::from_u128(u128::MAX),
            Scalar::from(2).pow_vartime(&[254, 0, 0, 0]),
        ];
        scalars.extend((0..24).map(|_| Scalar::random(&mut rng)));
        let bases = scalars
            .iter()
            .map(|_| G1Projective::random(&mut rng))
            .collect::<Vec<_>>();

        for (base, scalar) in bases.iter().zip(&scalars) {
            assert_eq!(multiexp_vartime(&[*base], &[*scalar]), base * scalar);
        }
        for len in 0..=scalars.len() {
            let expected: G1Projective = bases[..len]
                .iter()
                .zip(&scalars[..len])
                .map(|(base, scalar)| base * scalar)
                .sum();
            assert_eq!(multiexp_vartime(&bases[..len], &scalars[..len]), expected);
        }
    }

    #[test]
    fn wnaf_digits_represent_integer() {
        for value in [0, 1, 7, 8, 9, 15, 0x0123_4567_89ab_cdef, u64::MAX] {
            let digits = wnaf(&value.to_le_bytes());
            let sum = digits
                .iter()
                .rev()
                .fold(0, |sum, &digit| 2 * sum + i128::from(digit));
            assert_eq!(sum, i128::from(value));
            for (i, &digit) in digits.iter().enumerate() {
                if digit != 0 {
                    assert!(digit % 2 != 0 && (-7..=7).contains(&digit));
                    assert!(digits[i + 1..].iter().take(3).all(|&digit| digit == 0));
                }
            }
        }
        // The digits of 2^64 - 1 are -1 at bit 0 and 1 at bit 64, beyond the last byte.
        assert_eq!(wnaf(&[0xff; 8]).len(), 65);
    }

    #[test]
    fn wnaf_is_used_for_bls12_381_scalars() {
        assert!(is_little_endian::<bls12_381::Scalar>());
        // The test field is too small for the probe value, so it uses the fallback.
        assert!(!is_little_endian::<crate::tests::dummy_engine::Fr>());
    }
}
