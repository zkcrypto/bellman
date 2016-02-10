use super::bit::{Bit, add};

pub struct ChaCha {
    key: Vec<Bit>,
    nonce: Vec<Bit>,
    counter: u32
}

impl Iterator for ChaCha {
    type Item = Vec<Bit>;

    fn next(&mut self) -> Option<Vec<Bit>> {
        let state = State::new(&self.key, self.counter, &self.nonce);
        let mut working_state = state.clone();

        for _ in 0..10 {
            working_state.inner_block();
        }

        let state = state.add(&working_state);

        Some(state.buf.iter().map(|a| a.swap_endianness()).flat_map(|a: UInt32| a.bits.into_iter()).collect())
    }
}

impl ChaCha {
    pub fn new(key: &[Bit]) -> ChaCha {
        assert_eq!(key.len(), 256);

        ChaCha {
            key: key.iter().cloned().collect(),
            nonce: (0..96).map(|_| Bit::constant(false)).collect(),
            counter: 1
        }
    }
}

#[derive(Clone)]
struct State {
    buf: Vec<UInt32>
}

impl State {
    fn new(key: &[Bit], counter: u32, nonce: &[Bit]) -> State {
        /*
           The ChaCha20 state is initialized as follows:

           o  The first four words (0-3) are constants: 0x61707865, 0x3320646e,
              0x79622d32, 0x6b206574.

           o  The next eight words (4-11) are taken from the 256-bit key by
              reading the bytes in little-endian order, in 4-byte chunks.

           o  Word 12 is a block counter.  Since each block is 64-byte, a 32-bit
              word is enough for 256 gigabytes of data.

           o  Words 13-15 are a nonce, which should not be repeated for the same
              key.  The 13th word is the first 32 bits of the input nonce taken
              as a little-endian integer, while the 15th word is the last 32
              bits.
        */

        assert_eq!(key.len(), 256);
        assert_eq!(nonce.len(), 96);

        let mut bits = vec![];
        bits.push(UInt32::from(0x61707865));
        bits.push(UInt32::from(0x3320646e));
        bits.push(UInt32::from(0x79622d32));
        bits.push(UInt32::from(0x6b206574));

        for i in 0..8 {
            let i = i*32;

            bits.push(UInt32::from(&key[i..i+32]).swap_endianness());
        }

        bits.push(UInt32::from(counter));

        for i in 0..3 {
            let i = i*32;

            bits.push(UInt32::from(&nonce[i..i+32]).swap_endianness());
        }

        State {
            buf: bits
        }
    }

    pub fn get(&self, index: usize) -> UInt32 {
        self.buf[index].clone()
    }

    pub fn set(&mut self, index: usize, to: UInt32) {
        self.buf[index] = to;
    }

    pub fn inner_block(&mut self) {
        /*
            inner_block (state):
                Qround(state, 0, 4, 8,12)
                Qround(state, 1, 5, 9,13)
                Qround(state, 2, 6,10,14)
                Qround(state, 3, 7,11,15)
                Qround(state, 0, 5,10,15)
                Qround(state, 1, 6,11,12)
                Qround(state, 2, 7, 8,13)
                Qround(state, 3, 4, 9,14)
                end
        */
        self.quarter_round(0, 4, 8, 12);
        self.quarter_round(1, 5, 9, 13);
        self.quarter_round(2, 6,10, 14);
        self.quarter_round(3, 7,11, 15);
        self.quarter_round(0, 5,10, 15);
        self.quarter_round(1, 6,11, 12);
        self.quarter_round(2, 7, 8, 13);
        self.quarter_round(3, 4, 9, 14);
    }

    pub fn quarter_round(&mut self, x: usize, y: usize, z: usize, w: usize) {
        /*
           2.2.  A Quarter Round on the ChaCha State

           The ChaCha state does not have four integer numbers: it has 16.  So
           the quarter-round operation works on only four of them -- hence the
           name.  Each quarter round operates on four predetermined numbers in
           the ChaCha state.  We will denote by QUARTERROUND(x,y,z,w) a quarter-
           round operation on the numbers at indices x, y, z, and w of the
           ChaCha state when viewed as a vector.  For example, if we apply
           QUARTERROUND(1,5,9,13) to a state, this means running the quarter-
           round operation on the elements marked with an asterisk, while
           leaving the others alone:

              0  *a   2   3
              4  *b   6   7
              8  *c  10  11
             12  *d  14  15
        */

        let mut a = self.get(x);
        let mut b = self.get(y);
        let mut c = self.get(z);
        let mut d = self.get(w);

        quarter_round(&mut a, &mut b, &mut c, &mut d);

        self.set(x, a);
        self.set(y, b);
        self.set(z, c);
        self.set(w, d);
    }

    fn add(&self, other: &State) -> State {
        State {
            buf: self.buf.iter().zip(other.buf.iter()).map(|(a, b)| a.add(b)).collect()
        }
    }
}

#[derive(Clone)]
struct UInt32 {
    bits: Vec<Bit>
}

impl<'a> From<&'a [Bit]> for UInt32 {
    fn from(b: &'a [Bit]) -> UInt32 {
        assert_eq!(b.len(), 32);

        UInt32 {
            bits: Vec::from(b)
        }
    }
}

impl From<u32> for UInt32 {
    fn from(num: u32) -> UInt32 {
        UInt32 {
            bits: (0..32).map(|i| Bit::constant(num & (1 << i) != 0)).rev().collect()
        }
    }
}

impl UInt32 {
    fn add(&self, other: &UInt32) -> UInt32 {
        let a: Vec<_> = self.bits.iter().cloned().collect();
        let b: Vec<_> = other.bits.iter().cloned().collect();

        UInt32 {
            bits: add(&a, &b)
        }
    }

    fn swap_endianness(&self) -> UInt32 {
        UInt32 {
            bits: self.bits.chunks(8).rev().flat_map(|chunk| chunk.iter()).cloned().collect()
        }
    }

    fn xor(&self, other: &UInt32) -> UInt32 {
        UInt32 {
            bits: self.bits.iter().zip(other.bits.iter()).map(|(a, b)| a.xor(b)).collect()
        }
    }

    fn rotl(&self, by: usize) -> UInt32 {
        let by = by % 32;

        UInt32 {
            bits: self.bits[by..].iter()
                                 .chain(self.bits[0..by].iter())
                                 .cloned()
                                 .collect()
        }
    }
}

fn quarter_round(a: &mut UInt32, b: &mut UInt32, c: &mut UInt32, d: &mut UInt32)
{
    /*
       2.1.  The ChaCha Quarter Round

       The basic operation of the ChaCha algorithm is the quarter round.  It
       operates on four 32-bit unsigned integers, denoted a, b, c, and d.
       The operation is as follows (in C-like notation):

       1.  a += b; d ^= a; d <<<= 16;
       2.  c += d; b ^= c; b <<<= 12;
       3.  a += b; d ^= a; d <<<= 8;
       4.  c += d; b ^= c; b <<<= 7;

       Where "+" denotes integer addition modulo 2^32, "^" denotes a bitwise
       Exclusive OR (XOR), and "<<< n" denotes an n-bit left rotation
       (towards the high bits).

       For example, let's see the add, XOR, and roll operations from the
       fourth line with sample numbers:

       o  a = 0x11111111
       o  b = 0x01020304
       o  c = 0x77777777
       o  d = 0x01234567
       o  c = c + d = 0x77777777 + 0x01234567 = 0x789abcde
       o  b = b ^ c = 0x01020304 ^ 0x789abcde = 0x7998bfda
       o  b = b <<< 7 = 0x7998bfda <<< 7 = 0xcc5fed3c
    */
    macro_rules! permutation(
        ($a:ident, $b:ident, $c:ident, $amt:expr) => ({
            *($a) = ($a).add($b);
            *($c) = ($c).xor($a);
            *($c) = ($c).rotl($amt);
        })
    );
    permutation!(a, b, d, 16);
    permutation!(c, d, b, 12);
    permutation!(a, b, d, 8);
    permutation!(c, d, b, 7);
}


#[test]
fn test_chacha_proof() {
    use tinysnark::{self, FieldT};
    use super::circuit::{CircuitBuilder, Equals};

    tinysnark::init();

    let (public, private, mut circuit) = CircuitBuilder::new(512, 256);

    let private: Vec<_> = private.iter().map(|b| Bit::new(b)).collect();
    let mut stream = ChaCha::new(&private);

    circuit.constrain(stream.next().unwrap().must_equal(&public));

    let circuit = circuit.finalize();

    let mut input: Vec<FieldT> = (0..256).map(|_| FieldT::zero()).collect();

    let expected = vec![true, false, false, true, true, true, true, true, false, false, false, false, false, true, true, true, true, true, true, false, false, true, true, true, true, false, true, true, true, true, true, false, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, true, false, false, true, true, true, false, false, false, false, true, true, true, true, false, true, false, true, false, false, true, true, false, false, false, true, false, true, true, true, false, true, false, true, false, false, true, false, true, true, true, false, true, true, true, true, true, false, false, false, true, true, true, false, false, true, true, false, false, true, false, true, true, false, true, false, false, false, false, true, false, false, false, false, false, false, false, true, true, false, true, true, true, false, false, true, false, true, true, false, false, false, false, true, true, true, true, false, false, true, false, true, false, false, true, true, false, true, false, false, false, false, false, false, true, false, false, true, false, false, false, true, true, true, false, false, false, true, true, false, true, true, false, false, true, false, true, false, true, true, false, true, false, false, true, false, false, false, true, false, false, true, false, true, true, false, false, false, true, true, false, false, true, false, true, false, false, true, true, false, false, true, true, true, true, true, false, false, false, true, true, false, false, true, false, true, true, true, false, true, true, true, false, false, true, true, true, true, false, true, false, true, true, true, false, true, true, false, true, false, false, true, false, true, false, false, true, true, false, true, true, false, true, true, true, false, false, true, false, false, false, false, true, false, true, true, true, false, true, true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, true, false, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, true, true, true, false, true, false, true, false, true, false, true, true, true, false, false, false, true, false, false, true, true, false, false, true, true, true, false, true, true, false, false, false, false, false, true, true, true, false, true, false, false, true, true, false, true, true, false, false, false, false, false, true, true, true, false, false, true, true, true, false, true, false, true, false, true, false, false, true, true, false, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, true, true, true, true, false, false, true, false, true, false, false, false, false, true, false, true, false, false, false, true, false, false, false, false, true, false, true, false, true, true, true, true, true, false, true, true, false, true, false, false, false, true, false, true, true, false, true, false, true, true, false, false, true, true, true, false, false, false, false, true, false, false, false, false, true, false, true, false, false, false, false, true, true, true, true, true, false, true, false, false, true, false, true, true, false, true, true, true, true, false, false, true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, true];

    let mut output: Vec<FieldT> = expected.into_iter().map(|b| if b { FieldT::one() } else { FieldT::zero() }).collect();

    let proof = circuit.prove(&output, &input).unwrap();
    assert!(circuit.verify(&proof, &output));
}

#[cfg(test)]
mod test {
    use super::{quarter_round, UInt32, State, ChaCha};
    use super::super::bit::Bit;

    impl PartialEq for UInt32 {
        fn eq(&self, other: &UInt32) -> bool {
            for (a, b) in self.bits.iter().zip(other.bits.iter()) {
                if a.val(&[]) != b.val(&[]) {
                    return false;
                }
            }

            true
        }
    }

    impl PartialEq for State {
        fn eq(&self, other: &State) -> bool {
            for (a, b) in self.buf.iter().zip(other.buf.iter()) {
                if a != b {
                    return false;
                }
            }

            true
        }
    }

    impl<'a> From<&'a [u32; 16]> for State {
        fn from(nums: &'a [u32; 16]) -> State {
            State {
                buf: nums.iter().map(|&x| x.into()).collect()
            }
        }
    }

    fn bytes_to_bits(input: &[u8]) -> Vec<Bit> {
        let mut ret = vec![];

        for byte in input {
            ret.extend((0..8).map(|i| Bit::constant(byte & (1 << i) != 0)).rev());
        }

        ret
    }

    #[test]
    fn test_quarter_round() {
        /*
            2.1.1.  Test Vector for the ChaCha Quarter Round

               For a test vector, we will use the same numbers as in the example,
               adding something random for c.

               o  a = 0x11111111
               o  b = 0x01020304
               o  c = 0x9b8d6f43
               o  d = 0x01234567

               After running a Quarter Round on these four numbers, we get these:

               o  a = 0xea2a92f4
               o  b = 0xcb1cf8ce
               o  c = 0x4581472e
               o  d = 0x5881c4bb
        */
        let mut a = UInt32::from(0x11111111);
        let mut b = UInt32::from(0x01020304);
        let mut c = UInt32::from(0x9b8d6f43);
        let mut d = UInt32::from(0x01234567);

        quarter_round(&mut a, &mut b, &mut c, &mut d);

        assert!(UInt32::from(0xea2a92f4) == a);
        assert!(UInt32::from(0xcb1cf8ce) == b);
        assert!(UInt32::from(0x4581472e) == c);
        assert!(UInt32::from(0x5881c4bb) == d);
    }

    #[test]
    fn test_quarter_round_on_state() {
        /*
           2.2.1.  Test Vector for the Quarter Round on the ChaCha State

           For a test vector, we will use a ChaCha state that was generated
           randomly:

           Sample ChaCha State

               879531e0  c5ecf37d  516461b1  c9a62f8a
               44c20ef3  3390af7f  d9fc690b  2a5f714c
               53372767  b00a5631  974c541a  359e9963
               5c971061  3d631689  2098d9d6  91dbd320

           We will apply the QUARTERROUND(2,7,8,13) operation to this state.
           For obvious reasons, this one is part of what is called a "diagonal
           round":

           After applying QUARTERROUND(2,7,8,13)

               879531e0  c5ecf37d *bdb886dc  c9a62f8a
               44c20ef3  3390af7f  d9fc690b *cfacafd2
              *e46bea80  b00a5631  974c541a  359e9963
               5c971061 *ccc07c79  2098d9d6  91dbd320
        */

        let mut s = State::from(&[
            0x879531e0,  0xc5ecf37d,  0x516461b1,  0xc9a62f8a,
            0x44c20ef3,  0x3390af7f,  0xd9fc690b,  0x2a5f714c,
            0x53372767,  0xb00a5631,  0x974c541a,  0x359e9963,
            0x5c971061,  0x3d631689,  0x2098d9d6,  0x91dbd320
        ]);
        
        s.quarter_round(2, 7, 8, 13);

        assert!(s == State::from(&[
            0x879531e0,  0xc5ecf37d,  0xbdb886dc,  0xc9a62f8a,
            0x44c20ef3,  0x3390af7f,  0xd9fc690b,  0xcfacafd2,
            0xe46bea80,  0xb00a5631,  0x974c541a,  0x359e9963,
            0x5c971061,  0xccc07c79,  0x2098d9d6,  0x91dbd320
        ]));
    }

    #[test]
    fn test_round_function() {
        /*
           2.3.2.  Test Vector for the ChaCha20 Block Function

           For a test vector, we will use the following inputs to the ChaCha20
           block function:

           o  Key = 00:01:02:03:04:05:06:07:08:09:0a:0b:0c:0d:0e:0f:10:11:12:13:
              14:15:16:17:18:19:1a:1b:1c:1d:1e:1f.  The key is a sequence of
              octets with no particular structure before we copy it into the
              ChaCha state.

           o  Nonce = (00:00:00:09:00:00:00:4a:00:00:00:00)

           o  Block Count = 1.

           After setting up the ChaCha state, it looks like this:

           ChaCha state with the key setup.

               61707865  3320646e  79622d32  6b206574
               03020100  07060504  0b0a0908  0f0e0d0c
               13121110  17161514  1b1a1918  1f1e1d1c
               00000001  09000000  4a000000  00000000
        */

        let key = bytes_to_bits(&[0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,0x09,0x0a,0x0b,0x0c,0x0d,0x0e,0x0f,0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17,0x18,0x19,0x1a,0x1b,0x1c,0x1d,0x1e,0x1f]);
        let counter = 1;
        let nonce = bytes_to_bits(&[0x00, 0x00, 0x00, 0x09, 0x00, 0x00, 0x00, 0x4a, 0x00, 0x00, 0x00, 0x00]);

        let mut s = State::new(&key, counter, &nonce);
        let original_state = s.clone();

        assert!(s == State::from(&[
            0x61707865,  0x3320646e,  0x79622d32,  0x6b206574,
            0x03020100,  0x07060504,  0x0b0a0908,  0x0f0e0d0c,
            0x13121110,  0x17161514,  0x1b1a1918,  0x1f1e1d1c,
            0x00000001,  0x09000000,  0x4a000000,  0x00000000
        ]));

        /*
            After running 20 rounds (10 column rounds interleaved with 10
            "diagonal rounds"), the ChaCha state looks like this:

            ChaCha state after 20 rounds

               837778ab  e238d763  a67ae21e  5950bb2f
               c4f2d0c7  fc62bb2f  8fa018fc  3f5ec7b7
               335271c2  f29489f3  eabda8fc  82e46ebd
               d19c12b4  b04e16de  9e83d0cb  4e3c50a2
        */

        for _ in 0..10 {
            s.inner_block();
        }

        assert!(s == State::from(&[
            0x837778ab,  0xe238d763,  0xa67ae21e,  0x5950bb2f,
            0xc4f2d0c7,  0xfc62bb2f,  0x8fa018fc,  0x3f5ec7b7,
            0x335271c2,  0xf29489f3,  0xeabda8fc,  0x82e46ebd,
            0xd19c12b4,  0xb04e16de,  0x9e83d0cb,  0x4e3c50a2
        ]));
        
        let s = s.add(&original_state);

        /*
           Finally, we add the original state to the result (simple vector or
           matrix addition), giving this:

           ChaCha state at the end of the ChaCha20 operation

               e4e7f110  15593bd1  1fdd0f50  c47120a3
               c7f4d1c7  0368c033  9aaa2204  4e6cd4c3
               466482d2  09aa9f07  05d7c214  a2028bd9
               d19c12b5  b94e16de  e883d0cb  4e3c50a2
        */

        assert!(s == State::from(&[
            0xe4e7f110,  0x15593bd1,  0x1fdd0f50,  0xc47120a3,
            0xc7f4d1c7,  0x0368c033,  0x9aaa2204,  0x4e6cd4c3,
            0x466482d2,  0x09aa9f07,  0x05d7c214,  0xa2028bd9,
            0xd19c12b5,  0xb94e16de,  0xe883d0cb,  0x4e3c50a2
        ]));
    }
}
