//! The [BLAKE2s] hash function with personalization support.
//!
//! [BLAKE2s]: https://tools.ietf.org/html/rfc7693

use super::{boolean::Boolean, multieq::MultiEq, uint32::UInt32};
use crate::{ConstraintSystem, SynthesisError};
use ff::PrimeField;

/*
2.1.  Parameters
   The following table summarizes various parameters and their ranges:
                            | BLAKE2b          | BLAKE2s          |
              --------------+------------------+------------------+
               Bits in word | w = 64           | w = 32           |
               Rounds in F  | r = 12           | r = 10           |
               Block bytes  | bb = 128         | bb = 64          |
               Hash bytes   | 1 <= nn <= 64    | 1 <= nn <= 32    |
               Key bytes    | 0 <= kk <= 64    | 0 <= kk <= 32    |
               Input bytes  | 0 <= ll < 2**128 | 0 <= ll < 2**64  |
              --------------+------------------+------------------+
               G Rotation   | (R1, R2, R3, R4) | (R1, R2, R3, R4) |
                constants = | (32, 24, 16, 63) | (16, 12,  8,  7) |
              --------------+------------------+------------------+
*/

const R1: usize = 16;
const R2: usize = 12;
const R3: usize = 8;
const R4: usize = 7;

/*
          Round   |  0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 |
        ----------+-------------------------------------------------+
         SIGMA[0] |  0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 |
         SIGMA[1] | 14 10  4  8  9 15 13  6  1 12  0  2 11  7  5  3 |
         SIGMA[2] | 11  8 12  0  5  2 15 13 10 14  3  6  7  1  9  4 |
         SIGMA[3] |  7  9  3  1 13 12 11 14  2  6  5 10  4  0 15  8 |
         SIGMA[4] |  9  0  5  7  2  4 10 15 14  1 11 12  6  8  3 13 |
         SIGMA[5] |  2 12  6 10  0 11  8  3  4 13  7  5 15 14  1  9 |
         SIGMA[6] | 12  5  1 15 14 13  4 10  0  7  6  3  9  2  8 11 |
         SIGMA[7] | 13 11  7 14 12  1  3  9  5  0 15  4  8  6  2 10 |
         SIGMA[8] |  6 15 14  9 11  3  0  8 12  2 13  7  1  4 10  5 |
         SIGMA[9] | 10  2  8  4  7  6  1  5 15 11  9 14  3 12 13  0 |
        ----------+-------------------------------------------------+
*/

const SIGMA: [[usize; 16]; 10] = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
];

/*
3.1.  Mixing Function G
   The G primitive function mixes two input words, "x" and "y", into
   four words indexed by "a", "b", "c", and "d" in the working vector
   v[0..15].  The full modified vector is returned.  The rotation
   constants (R1, R2, R3, R4) are given in Section 2.1.
       FUNCTION G( v[0..15], a, b, c, d, x, y )
       |
       |   v[a] := (v[a] + v[b] + x) mod 2**w
       |   v[d] := (v[d] ^ v[a]) >>> R1
       |   v[c] := (v[c] + v[d])     mod 2**w
       |   v[b] := (v[b] ^ v[c]) >>> R2
       |   v[a] := (v[a] + v[b] + y) mod 2**w
       |   v[d] := (v[d] ^ v[a]) >>> R3
       |   v[c] := (v[c] + v[d])     mod 2**w
       |   v[b] := (v[b] ^ v[c]) >>> R4
       |
       |   RETURN v[0..15]
       |
       END FUNCTION.
*/

fn mixing_g<Scalar: PrimeField, CS: ConstraintSystem<Scalar>, M>(
    mut cs: M,
    v: &mut [UInt32],
    a: usize,
    b: usize,
    c: usize,
    d: usize,
    x: &UInt32,
    y: &UInt32,
) -> Result<(), SynthesisError>
where
    M: ConstraintSystem<Scalar, Root = MultiEq<Scalar, CS>>,
{
    v[a] = UInt32::addmany(
        cs.namespace(|| "mixing step 1"),
        &[v[a].clone(), v[b].clone(), x.clone()],
    )?;
    v[d] = v[d].xor(cs.namespace(|| "mixing step 2"), &v[a])?.rotr(R1);
    v[c] = UInt32::addmany(
        cs.namespace(|| "mixing step 3"),
        &[v[c].clone(), v[d].clone()],
    )?;
    v[b] = v[b].xor(cs.namespace(|| "mixing step 4"), &v[c])?.rotr(R2);
    v[a] = UInt32::addmany(
        cs.namespace(|| "mixing step 5"),
        &[v[a].clone(), v[b].clone(), y.clone()],
    )?;
    v[d] = v[d].xor(cs.namespace(|| "mixing step 6"), &v[a])?.rotr(R3);
    v[c] = UInt32::addmany(
        cs.namespace(|| "mixing step 7"),
        &[v[c].clone(), v[d].clone()],
    )?;
    v[b] = v[b].xor(cs.namespace(|| "mixing step 8"), &v[c])?.rotr(R4);

    Ok(())
}

/*
3.2.  Compression Function F
   Compression function F takes as an argument the state vector "h",
   message block vector "m" (last block is padded with zeros to full
   block size, if required), 2w-bit offset counter "t", and final block
   indicator flag "f".  Local vector v[0..15] is used in processing.  F
   returns a new state vector.  The number of rounds, "r", is 12 for
   BLAKE2b and 10 for BLAKE2s.  Rounds are numbered from 0 to r - 1.
       FUNCTION F( h[0..7], m[0..15], t, f )
       |
       |      // Initialize local work vector v[0..15]
       |      v[0..7] := h[0..7]              // First half from state.
       |      v[8..15] := IV[0..7]            // Second half from IV.
       |
       |      v[12] := v[12] ^ (t mod 2**w)   // Low word of the offset.
       |      v[13] := v[13] ^ (t >> w)       // High word.
       |
       |      IF f = TRUE THEN                // last block flag?
       |      |   v[14] := v[14] ^ 0xFF..FF   // Invert all bits.
       |      END IF.
       |
       |      // Cryptographic mixing
       |      FOR i = 0 TO r - 1 DO           // Ten or twelve rounds.
       |      |
       |      |   // Message word selection permutation for this round.
       |      |   s[0..15] := SIGMA[i mod 10][0..15]
       |      |
       |      |   v := G( v, 0, 4,  8, 12, m[s[ 0]], m[s[ 1]] )
       |      |   v := G( v, 1, 5,  9, 13, m[s[ 2]], m[s[ 3]] )
       |      |   v := G( v, 2, 6, 10, 14, m[s[ 4]], m[s[ 5]] )
       |      |   v := G( v, 3, 7, 11, 15, m[s[ 6]], m[s[ 7]] )
       |      |
       |      |   v := G( v, 0, 5, 10, 15, m[s[ 8]], m[s[ 9]] )
       |      |   v := G( v, 1, 6, 11, 12, m[s[10]], m[s[11]] )
       |      |   v := G( v, 2, 7,  8, 13, m[s[12]], m[s[13]] )
       |      |   v := G( v, 3, 4,  9, 14, m[s[14]], m[s[15]] )
       |      |
       |      END FOR
       |
       |      FOR i = 0 TO 7 DO               // XOR the two halves.
       |      |   h[i] := h[i] ^ v[i] ^ v[i + 8]
       |      END FOR.
       |
       |      RETURN h[0..7]                  // New state.
       |
       END FUNCTION.
*/

fn blake2s_compression<Scalar: PrimeField, CS: ConstraintSystem<Scalar>>(
    mut cs: CS,
    h: &mut [UInt32],
    m: &[UInt32],
    t: u64,
    f: bool,
) -> Result<(), SynthesisError> {
    assert_eq!(h.len(), 8);
    assert_eq!(m.len(), 16);

    /*
    static const uint32_t blake2s_iv[8] =
    {
        0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
        0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19
    };
    */

    let mut v = Vec::with_capacity(16);
    v.extend_from_slice(h);
    v.push(UInt32::constant(0x6A09E667));
    v.push(UInt32::constant(0xBB67AE85));
    v.push(UInt32::constant(0x3C6EF372));
    v.push(UInt32::constant(0xA54FF53A));
    v.push(UInt32::constant(0x510E527F));
    v.push(UInt32::constant(0x9B05688C));
    v.push(UInt32::constant(0x1F83D9AB));
    v.push(UInt32::constant(0x5BE0CD19));

    assert_eq!(v.len(), 16);

    v[12] = v[12].xor(cs.namespace(|| "first xor"), &UInt32::constant(t as u32))?;
    v[13] = v[13].xor(
        cs.namespace(|| "second xor"),
        &UInt32::constant((t >> 32) as u32),
    )?;

    if f {
        v[14] = v[14].xor(
            cs.namespace(|| "third xor"),
            &UInt32::constant(u32::max_value()),
        )?;
    }

    {
        let mut cs = MultiEq::new(&mut cs);

        for i in 0..10 {
            let mut cs = cs.namespace(|| format!("round {}", i));

            let s = SIGMA[i % 10];

            mixing_g(
                cs.namespace(|| "mixing invocation 1"),
                &mut v,
                0,
                4,
                8,
                12,
                &m[s[0]],
                &m[s[1]],
            )?;
            mixing_g(
                cs.namespace(|| "mixing invocation 2"),
                &mut v,
                1,
                5,
                9,
                13,
                &m[s[2]],
                &m[s[3]],
            )?;
            mixing_g(
                cs.namespace(|| "mixing invocation 3"),
                &mut v,
                2,
                6,
                10,
                14,
                &m[s[4]],
                &m[s[5]],
            )?;
            mixing_g(
                cs.namespace(|| "mixing invocation 4"),
                &mut v,
                3,
                7,
                11,
                15,
                &m[s[6]],
                &m[s[7]],
            )?;

            mixing_g(
                cs.namespace(|| "mixing invocation 5"),
                &mut v,
                0,
                5,
                10,
                15,
                &m[s[8]],
                &m[s[9]],
            )?;
            mixing_g(
                cs.namespace(|| "mixing invocation 6"),
                &mut v,
                1,
                6,
                11,
                12,
                &m[s[10]],
                &m[s[11]],
            )?;
            mixing_g(
                cs.namespace(|| "mixing invocation 7"),
                &mut v,
                2,
                7,
                8,
                13,
                &m[s[12]],
                &m[s[13]],
            )?;
            mixing_g(
                cs.namespace(|| "mixing invocation 8"),
                &mut v,
                3,
                4,
                9,
                14,
                &m[s[14]],
                &m[s[15]],
            )?;
        }
    }

    for i in 0..8 {
        let mut cs = cs.namespace(|| format!("h[{i}] ^ v[{i}] ^ v[{i} + 8]", i = i));

        h[i] = h[i].xor(cs.namespace(|| "first xor"), &v[i])?;
        h[i] = h[i].xor(cs.namespace(|| "second xor"), &v[i + 8])?;
    }

    Ok(())
}

/*
        FUNCTION BLAKE2( d[0..dd-1], ll, kk, nn )
        |
        |     h[0..7] := IV[0..7]          // Initialization Vector.
        |
        |     // Parameter block p[0]
        |     h[0] := h[0] ^ 0x01010000 ^ (kk << 8) ^ nn
        |
        |     // Process padded key and data blocks
        |     IF dd > 1 THEN
        |     |       FOR i = 0 TO dd - 2 DO
        |     |       |       h := F( h, d[i], (i + 1) * bb, FALSE )
        |     |       END FOR.
        |     END IF.
        |
        |     // Final block.
        |     IF kk = 0 THEN
        |     |       h := F( h, d[dd - 1], ll, TRUE )
        |     ELSE
        |     |       h := F( h, d[dd - 1], ll + bb, TRUE )
        |     END IF.
        |
        |     RETURN first "nn" bytes from little-endian word array h[].
        |
        END FUNCTION.
*/

pub fn blake2s<Scalar: PrimeField, CS: ConstraintSystem<Scalar>>(
    mut cs: CS,
    input: &[Boolean],
    personalization: &[u8],
) -> Result<Vec<Boolean>, SynthesisError> {
    use byteorder::{ByteOrder, LittleEndian};

    assert_eq!(personalization.len(), 8);
    assert!(input.len() % 8 == 0);

    let mut h = Vec::with_capacity(8);
    h.push(UInt32::constant(0x6A09E667 ^ 0x01010000 ^ 32));
    h.push(UInt32::constant(0xBB67AE85));
    h.push(UInt32::constant(0x3C6EF372));
    h.push(UInt32::constant(0xA54FF53A));
    h.push(UInt32::constant(0x510E527F));
    h.push(UInt32::constant(0x9B05688C));

    // Personalization is stored here
    h.push(UInt32::constant(
        0x1F83D9AB ^ LittleEndian::read_u32(&personalization[0..4]),
    ));
    h.push(UInt32::constant(
        0x5BE0CD19 ^ LittleEndian::read_u32(&personalization[4..8]),
    ));

    let mut blocks: Vec<Vec<UInt32>> = vec![];

    for block in input.chunks(512) {
        let mut this_block = Vec::with_capacity(16);
        for word in block.chunks(32) {
            let mut tmp = word.to_vec();
            while tmp.len() < 32 {
                tmp.push(Boolean::constant(false));
            }
            this_block.push(UInt32::from_bits(&tmp));
        }
        while this_block.len() < 16 {
            this_block.push(UInt32::constant(0));
        }
        blocks.push(this_block);
    }

    if blocks.is_empty() {
        blocks.push((0..16).map(|_| UInt32::constant(0)).collect());
    }

    for (i, block) in blocks[0..blocks.len() - 1].iter().enumerate() {
        let cs = cs.namespace(|| format!("block {}", i));

        blake2s_compression(cs, &mut h, block, ((i as u64) + 1) * 64, false)?;
    }

    {
        let cs = cs.namespace(|| "final block");

        blake2s_compression(
            cs,
            &mut h,
            &blocks[blocks.len() - 1],
            (input.len() / 8) as u64,
            true,
        )?;
    }

    Ok(h.into_iter().flat_map(|b| b.into_bits()).collect())
}

#[cfg(test)]
mod test {
    use blake2s_simd::Params as Blake2sParams;
    use bls12_381::Scalar;
    use hex_literal::hex;
    use rand_core::{RngCore, SeedableRng};
    use rand_xorshift::XorShiftRng;

    use super::blake2s;
    use crate::gadgets::boolean::{AllocatedBit, Boolean};
    use crate::gadgets::test::TestConstraintSystem;
    use crate::ConstraintSystem;

    #[test]
    fn test_blank_hash() {
        let mut cs = TestConstraintSystem::<Scalar>::new();
        let input_bits = vec![];
        let out = blake2s(&mut cs, &input_bits, b"12345678").unwrap();
        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 0);

        // >>> import blake2s from hashlib
        // >>> h = blake2s(digest_size=32, person=b'12345678')
        // >>> h.hexdigest()
        let expected = hex!("c59f682376d137f3f255e671e207d1f2374ebe504e9314208a52d9f88d69e8c8");

        let mut out = out.into_iter();
        for b in expected.iter() {
            for i in 0..8 {
                let c = out.next().unwrap().get_value().unwrap();

                assert_eq!(c, (b >> i) & 1u8 == 1u8);
            }
        }
    }

    #[test]
    fn test_blake2s_constraints() {
        let mut cs = TestConstraintSystem::<Scalar>::new();
        let input_bits: Vec<_> = (0..512)
            .map(|i| {
                AllocatedBit::alloc(cs.namespace(|| format!("input bit {}", i)), Some(true))
                    .unwrap()
                    .into()
            })
            .collect();
        blake2s(&mut cs, &input_bits, b"12345678").unwrap();
        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 21518);
    }

    #[test]
    fn test_blake2s_precomp_constraints() {
        // Test that 512 fixed leading bits (constants)
        // doesn't result in more constraints.

        let mut cs = TestConstraintSystem::<Scalar>::new();
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);
        let input_bits: Vec<_> = (0..512)
            .map(|_| Boolean::constant(rng.next_u32() % 2 != 0))
            .chain((0..512).map(|i| {
                AllocatedBit::alloc(cs.namespace(|| format!("input bit {}", i)), Some(true))
                    .unwrap()
                    .into()
            }))
            .collect();
        blake2s(&mut cs, &input_bits, b"12345678").unwrap();
        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 21518);
    }

    #[test]
    fn test_blake2s_constant_constraints() {
        let mut cs = TestConstraintSystem::<Scalar>::new();
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);
        let input_bits: Vec<_> = (0..512)
            .map(|_| Boolean::constant(rng.next_u32() % 2 != 0))
            .collect();
        blake2s(&mut cs, &input_bits, b"12345678").unwrap();
        assert_eq!(cs.num_constraints(), 0);
    }

    #[test]
    fn test_blake2s() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for input_len in (0..32).chain((32..256).filter(|a| a % 8 == 0)) {
            let mut h = Blake2sParams::new()
                .hash_length(32)
                .personal(b"12345678")
                .to_state();

            let data: Vec<u8> = (0..input_len).map(|_| rng.next_u32() as u8).collect();

            h.update(&data);

            let hash_result = h.finalize();

            let mut cs = TestConstraintSystem::<Scalar>::new();

            let mut input_bits = vec![];

            for (byte_i, input_byte) in data.into_iter().enumerate() {
                for bit_i in 0..8 {
                    let cs = cs.namespace(|| format!("input bit {} {}", byte_i, bit_i));

                    input_bits.push(
                        AllocatedBit::alloc(cs, Some((input_byte >> bit_i) & 1u8 == 1u8))
                            .unwrap()
                            .into(),
                    );
                }
            }

            let r = blake2s(&mut cs, &input_bits, b"12345678").unwrap();

            assert!(cs.is_satisfied());

            let mut s = hash_result
                .as_ref()
                .iter()
                .flat_map(|&byte| (0..8).map(move |i| (byte >> i) & 1u8 == 1u8));

            for b in r {
                match b {
                    Boolean::Is(b) => {
                        assert!(s.next().unwrap() == b.get_value().unwrap());
                    }
                    Boolean::Not(b) => {
                        assert!(s.next().unwrap() != b.get_value().unwrap());
                    }
                    Boolean::Constant(b) => {
                        assert!(input_len == 0);
                        assert!(s.next().unwrap() == b);
                    }
                }
            }
        }
    }

    #[test]
    fn test_blake2s_256_vars() {
        let data: Vec<u8> = hex!("be9f9c485e670acce8b1516a378176161b20583637b6f1c536fbc1158a0a3296831df2920e57a442d5738f4be4dd6be89dd7913fc8b4d1c0a815646a4d674b77f7caf313bd880bf759fcac27037c48c2b2a20acd2fd5248e3be426c84a341c0a3c63eaf36e0d537d10b8db5c6e4c801832c41eb1a3ed602177acded8b4b803bd34339d99a18b71df399641cc8dfae2ad193fcd74b5913e704551777160d14c78f2e8d5c32716a8599c1080cb89a40ccd6ba596694a8b4a065d9f2d0667ef423ed2e418093caff884540858b4f4b62acd47edcea880523e1b1cda8eb225c128c2e9e83f14f6e7448c5733a195cac7d79a53dde5083172462c45b2f799e42af1c9").to_vec();
        assert_eq!(data.len(), 256);

        let mut cs = TestConstraintSystem::<Scalar>::new();

        let mut input_bits = vec![];

        for (byte_i, input_byte) in data.into_iter().enumerate() {
            for bit_i in 0..8 {
                let cs = cs.namespace(|| format!("input bit {} {}", byte_i, bit_i));

                input_bits.push(
                    AllocatedBit::alloc(cs, Some((input_byte >> bit_i) & 1u8 == 1u8))
                        .unwrap()
                        .into(),
                );
            }
        }

        let r = blake2s(&mut cs, &input_bits, b"12345678").unwrap();

        assert!(cs.is_satisfied());

        let expected = hex!("0af5695115ced92c8a0341e43869209636e9aa6472e4576f0f2b996cf812b30e");

        let mut out = r.into_iter();
        for b in expected.iter() {
            for i in 0..8 {
                let c = out.next().unwrap().get_value().unwrap();

                assert_eq!(c, (b >> i) & 1u8 == 1u8);
            }
        }
    }

    #[test]
    fn test_blake2s_700_vars() {
        let data: Vec<u8> = hex!("5dcfe8bab4c758d2eb1ddb7ef337583e0df3e2c358e1755b7cd303a658de9a1227eed1d1114179a5c3c38d692ff2cf2d4e5c92a9516de750106774bbf9f7d063f707f4c9b6a02c0a77e4feb99e036c3ccaee7d1a31cb144093aa074bc9da608f8ff30b39c3c60e4a243cc0bbd406d1262a7d6607b31c60275c6bcc8b0ac49a06a4b629a98693c5f7640f3bca45e4977cfabc5b17f52838af3433b1fd407dbbdc131e8e4bd58bcee85bbab4b57b656c6a2ec6cf852525bc8423675e2bf29159139cd5df99db94719f3f7167230e0d5bd76f6d7891b656732cef9c3c0d48a5fa3d7a879988157b39015a85451b25af0301ca5e759ac35fea79dca38c673ec6db9f3885d9103e2dcb3304bd3d59b0b1d01babc97ef8a74d91b6ab6bf50f29eb5adf7250a28fd85db37bff0133193635da69caeefc72979cf3bef1d2896d847eea7e8a81e0927893dbd010feb6fb845d0399007d9a148a0596d86cd8f4192631f975c560f4de8da5f712c161342063af3c11029d93d6df7ff46db48343499de9ec4786cac059c4025ef418c9fe40132428ff8b91259d71d1709ff066add84ae944b45a817f60b4c1bf719e39ae23e9b413469db2310793e9137cf38741e5dd2a3c138a566dbde1950c00071b20ac457b46ba9b0a7ebdddcc212bd228d2a4c4146a970e54158477247c27871af1564b176576e9fd43bf63740bf77434bc4ea3b1a4b430e1a11714bf43160145578a575c3f78ddeaa48de97f73460f26f8df2b5d63e31800100d16bc27160fea5ced5a977ef541cfe8dadc7b3991ed1c0d4f16a3076bbfed96ba3e155113e794987af8abb133f06feefabc2ac32eb4d4d4ba1541ca08b9e518d2e74b7f946b0cbd2663d58c689359b9a565821acc619011233d1011963fa302cde34fc9c5ba2e03eeb2512f547391e940d56218e22ae325f2dfa38d4bae35744ee707aa5dc9c17674025d15390a08f5c452343546ef6da0f7").to_vec();
        assert_eq!(data.len(), 700);

        let mut cs = TestConstraintSystem::<Scalar>::new();

        let mut input_bits = vec![];

        for (byte_i, input_byte) in data.into_iter().enumerate() {
            for bit_i in 0..8 {
                let cs = cs.namespace(|| format!("input bit {} {}", byte_i, bit_i));

                input_bits.push(
                    AllocatedBit::alloc(cs, Some((input_byte >> bit_i) & 1u8 == 1u8))
                        .unwrap()
                        .into(),
                );
            }
        }

        let r = blake2s(&mut cs, &input_bits, b"12345678").unwrap();

        assert!(cs.is_satisfied());

        let expected = hex!("2ab8f0683167ba220eef19dccf4f9b1a8193cc09b35e0235842323950530f18a");

        let mut out = r.into_iter();
        for b in expected.iter() {
            for i in 0..8 {
                let c = out.next().unwrap().get_value().unwrap();

                assert_eq!(c, (b >> i) & 1u8 == 1u8);
            }
        }
    }

    #[test]
    fn test_blake2s_test_vectors() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let expecteds = [
            hex!("a1309e334376c8f36a736a4ab0e691ef931ee3ebdb9ea96187127136fea622a1"),
            hex!("82fefff60f265cea255252f7c194a7f93965dffee0609ef74eb67f0d76cd41c6"),
        ];
        for i in 0..2 {
            let mut h = Blake2sParams::new()
                .hash_length(32)
                .personal(b"12345678")
                .to_state();
            let input_len = 1024;
            let data: Vec<u8> = (0..input_len).map(|_| rng.next_u32() as u8).collect();

            h.update(&data);

            let hash_result = h.finalize();

            let mut cs = TestConstraintSystem::<Scalar>::new();

            let mut input_bits = vec![];

            for (byte_i, input_byte) in data.into_iter().enumerate() {
                for bit_i in 0..8 {
                    let cs = cs.namespace(|| format!("input bit {} {}", byte_i, bit_i));

                    input_bits.push(
                        AllocatedBit::alloc(cs, Some((input_byte >> bit_i) & 1u8 == 1u8))
                            .unwrap()
                            .into(),
                    );
                }
            }

            let r = blake2s(&mut cs, &input_bits, b"12345678").unwrap();

            assert!(cs.is_satisfied());

            let mut s = hash_result
                .as_ref()
                .iter()
                .flat_map(|&byte| (0..8).map(move |i| (byte >> i) & 1u8 == 1u8));

            for b in r {
                match b {
                    Boolean::Is(b) => {
                        assert!(s.next().unwrap() == b.get_value().unwrap());
                    }
                    Boolean::Not(b) => {
                        assert!(s.next().unwrap() != b.get_value().unwrap());
                    }
                    Boolean::Constant(b) => {
                        assert!(input_len == 0);
                        assert!(s.next().unwrap() == b);
                    }
                }
            }

            assert_eq!(expecteds[i], hash_result.as_bytes());
        }
    }
}
