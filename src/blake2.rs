use super::bit::{Bit, add};
use std::ops::{Index, IndexMut};

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
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]
];

#[derive(Clone)]
struct UInt32(Vec<Bit>);

impl<'a> From<&'a [Bit]> for UInt32 {
    fn from(b: &'a [Bit]) -> UInt32 {
        assert_eq!(b.len(), 32);

        UInt32(Vec::from(b))
    }
}

impl From<u64> for UInt32 {
    fn from(num: u64) -> UInt32 {
        UInt32((0..32).map(|i| Bit::constant(num & (1 << i) != 0)).rev().collect())
    }
}

impl UInt32 {
    fn add(&self, other: &UInt32) -> UInt32 {
        UInt32(add(&self.0, &other.0))
    }

    fn xor(&self, other: &UInt32) -> UInt32 {
        UInt32((self.0).iter().zip((other.0).iter()).map(|(a, b)| a.xor(b)).collect())
    }

    fn rotr(&self, by: usize) -> UInt32 {
        let by = by % 32;

        UInt32(self.0[(self.0.len() - by)..].iter()
               .chain(self.0[0..(self.0.len() - by)].iter())
               .cloned()
               .collect())
    }
}

#[derive(Clone)]
struct State(Vec<UInt32>);

impl Index<usize> for State {
    type Output = UInt32;

    fn index<'a>(&'a self, _index: usize) -> &'a UInt32 {
        &(self.0)[_index]
    }
}

impl IndexMut<usize> for State {
    fn index_mut<'a>(&'a mut self, _index: usize) -> &'a mut UInt32 {
        &mut (self.0)[_index]
    }
}

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

fn G(v: &mut State, a: usize, b: usize, c: usize, d: usize, x: &UInt32, y: &UInt32) {
    v[a] = v[a].add(&v[b]).add(x);    // v[a] := (v[a] + v[b] + x) mod 2**w
    v[d] = v[d].xor(&v[a]).rotr(R1);  // v[d] := (v[d] ^ v[a]) >>> R1
    v[c] = v[c].add(&v[d]);           // v[c] := (v[c] + v[d])     mod 2**w
    v[b] = v[b].xor(&v[c]).rotr(R2);  // v[b] := (v[b] ^ v[c]) >>> R2
    v[a] = v[a].add(&v[b]).add(y);    // v[a] := (v[a] + v[b] + y) mod 2**w
    v[d] = v[d].xor(&v[a]).rotr(R3);  // v[d] := (v[d] ^ v[a]) >>> R3
    v[c] = v[c].add(&v[d]);           // v[c] := (v[c] + v[d])     mod 2**w
    v[b] = v[b].xor(&v[c]).rotr(R4);  // v[b] := (v[b] ^ v[c]) >>> R4
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

fn blake2_compression(h: &mut [UInt32], m: &[UInt32], t: UInt32, f: bool) {
    assert_eq!(h.len(), 8);
    assert_eq!(m.len(), 16);

    /*
   static const uint32_t blake2s_iv[8] =
   {
       0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
       0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19
   };
   */

    let mut v = vec![];
    v.extend_from_slice(h);
    v.push(UInt32::from(0x6A09E667));
    v.push(UInt32::from(0xBB67AE85));
    v.push(UInt32::from(0x3C6EF372));
    v.push(UInt32::from(0xA54FF53A));
    v.push(UInt32::from(0x510E527F));
    v.push(UInt32::from(0x9B05688C));
    v.push(UInt32::from(0x1F83D9AB));
    v.push(UInt32::from(0x5BE0CD19));

    assert_eq!(v.len(), 16);

    let mut v = State(v);

    // TODO: the following is omitted currently!
    /*
       |      v[12] := v[12] ^ (t mod 2**w)   // Low word of the offset.
       |      v[13] := v[13] ^ (t >> w)       // High word.
    */

    if f {
        v[14] = v[14].xor(&UInt32::from(0xffffffff));
    }

    /*

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
    */

    for i in 0..10 {
        let s = SIGMA[i % 10];

        G(&mut v, 0, 4, 8, 12,  &m[s[ 0]], &m[s[ 1]]);
        G(&mut v, 1, 5, 9, 13,  &m[s[ 2]], &m[s[ 3]]);
        G(&mut v, 2, 6, 10, 14, &m[s[ 4]], &m[s[ 5]]);
        G(&mut v, 3, 7, 11, 15, &m[s[ 6]], &m[s[ 7]]);

        G(&mut v, 0, 4, 10, 15, &m[s[ 8]], &m[s[ 9]]);
        G(&mut v, 1, 5, 11, 12, &m[s[10]], &m[s[11]]);
        G(&mut v, 2, 6, 8, 13,  &m[s[12]], &m[s[13]]);
        G(&mut v, 3, 7, 9, 14,  &m[s[14]], &m[s[15]]);
    }

    /*
       |      FOR i = 0 TO 7 DO               // XOR the two halves.
       |      |   h[i] := h[i] ^ v[i] ^ v[i + 8]
       |      END FOR.
    */

    for i in 0..8 {
        h[i] = h[i].xor(&v[i]).xor(&v[i+8]);
    }
}

#[test]
fn test_compression() {
    use tinysnark::{self, FieldT};
    use super::circuit::{CircuitBuilder, Equals};

    tinysnark::init();

    let (public, private, mut circuit) = CircuitBuilder::new(256, 512);

    let private: Vec<_> = private.iter().map(|b| Bit::new(b)).collect();

    let mut state = (0..8).map(|_| UInt32::from(0x00000000)).collect::<Vec<_>>();
    let message = (0..16).map(|i| UInt32::from(&private[(i*32)..((i*32)+32)])).collect::<Vec<_>>();

    blake2_compression(&mut state, &message, UInt32::from(0x00000000), false);

    let state: Vec<Bit> = state.into_iter().flat_map(|x| x.0.into_iter()).collect();

    circuit.constrain(state.must_equal(&public));

    let circuit = circuit.finalize();

    println!("NUMBER OF CONSTRAINTS: {}", circuit.num_constraints());
}