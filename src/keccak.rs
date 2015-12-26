//use tinysnark::FieldT;

const keccakf_rndc: [u64; 24] = 
[
    0x0000000000000001, 0x0000000000008082, 0x800000000000808a,
    0x8000000080008000, 0x000000000000808b, 0x0000000080000001,
    0x8000000080008081, 0x8000000000008009, 0x000000000000008a,
    0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
    0x000000008000808b, 0x800000000000008b, 0x8000000000008089,
    0x8000000000008003, 0x8000000000008002, 0x8000000000000080, 
    0x000000000000800a, 0x800000008000000a, 0x8000000080008081,
    0x8000000000008080, 0x0000000080000001, 0x8000000080008008
];

const keccakf_rotc: [usize; 24] = 
[
    1,  3,  6,  10, 15, 21, 28, 36, 45, 55, 2,  14, 
    27, 41, 56, 8,  25, 43, 62, 18, 39, 61, 20, 44
];

const keccakf_piln: [usize; 24] = 
[
    10, 7,  11, 17, 18, 3, 5,  16, 8,  21, 24, 4, 
    15, 23, 19, 13, 12, 2, 20, 14, 22, 9,  6,  1 
];

fn keccakf(st: &mut [Chunk; 25], rounds: usize)
{
    for round in 0..rounds {
        /*
        // Theta
        for (i = 0; i < 5; i++)     
            bc[i] = st[i] ^ st[i + 5] ^ st[i + 10] ^ st[i + 15] ^ st[i + 20];
        */

        // TODO: Rust arrays don't implement FromIterator.
        let mut bc: [Option<Chunk>; 5] = [None, None, None, None, None];

        for i in 0..5 {
            bc[i] = Some(st[i]
                         .xor(&st[i+5])
                         .xor(&st[i+10])
                         .xor(&st[i+15])
                         .xor(&st[i+20]));
        }

        let mut bc: [Chunk; 5] = [bc[0].take().unwrap(),
                                  bc[1].take().unwrap(),
                                  bc[2].take().unwrap(),
                                  bc[3].take().unwrap(),
                                  bc[4].take().unwrap()];

        /*
        for (i = 0; i < 5; i++) {
            t = bc[(i + 4) % 5] ^ ROTL64(bc[(i + 1) % 5], 1);
            for (j = 0; j < 25; j += 5)
                st[j + i] ^= t;
        }
        */

        for i in 0..5 {
            let tmp = bc[(i + 4) % 5].xor(&bc[(i + 1) % 5].rotl(1));

            for j in (0..25).filter(|a| a % 5 == 0) {
                st[j + i] = tmp.xor(&st[j + i]);
            }
        }

        {
            /*
            // Rho Pi
            t = st[1];
            for (i = 0; i < 24; i++) {
                j = keccakf_piln[i];
                bc[0] = st[j];
                st[j] = ROTL64(t, keccakf_rotc[i]);
                t = bc[0];
            }
            */
            let mut tmp = st[1].clone();

            for i in 0..24 {
                let j = keccakf_piln[i];

                bc[0] = st[j].clone();
                st[j] = tmp.rotl(keccakf_rotc[i]);
                tmp = bc[0].clone();
            }
        }

        {
            /*
            //  Chi
            for (j = 0; j < 25; j += 5) {
                for (i = 0; i < 5; i++)
                    bc[i] = st[j + i];
                for (i = 0; i < 5; i++)
                    st[j + i] ^= (~bc[(i + 1) % 5]) & bc[(i + 2) % 5];
            }
            */

            for j in (0..25).filter(|a| a % 5 == 0) {
                for i in 0..5 {
                    bc[i] = st[j + i].clone();
                }

                for i in 0..5 {
                    st[j + i] = st[j + i].xor(&bc[(i + 1) % 5].notand(&bc[(i + 2) % 5]));
                }
            }
        }

        /*
        //  Iota
        st[0] ^= keccakf_rndc[round];
        */

        st[0] = st[0].xor(&keccakf_rndc[round].into());
    }
}

// TODO: don't return a vec. currently don't have any
// more patience for rust's awful arrays
fn keccak256(mut input: &[[Bit; 8]]) -> Vec<Bit> {
    assert_eq!(input.len(), 144);

    let mut st: [Chunk; 25] = [Chunk::from(0), Chunk::from(0), Chunk::from(0), Chunk::from(0), Chunk::from(0),
                               Chunk::from(0), Chunk::from(0), Chunk::from(0), Chunk::from(0), Chunk::from(0), 
                               Chunk::from(0), Chunk::from(0), Chunk::from(0), Chunk::from(0), Chunk::from(0), 
                               Chunk::from(0), Chunk::from(0), Chunk::from(0), Chunk::from(0), Chunk::from(0), 
                               Chunk::from(0), Chunk::from(0), Chunk::from(0), Chunk::from(0), Chunk::from(0)
                              ];

    let mdlen = 32; // 256 bit
    let rsiz = 200 - 2 * mdlen;
    let rsizw = rsiz / 8;

    for i in 0..rsizw {
        let j = i * 8;
        st[i] = st[i].xor(&Chunk::from(&input[j..(j+8)]));
    }

    keccakf(&mut st, 24);

    let mut v = vec![];
    for i in 0..4 {
        // due to endianness...
        let tmp: Vec<_> = st[i].bits.chunks(8).rev().flat_map(|x| x.iter()).map(|x| x.clone()).collect();
        v.extend_from_slice(&tmp);
    }

    assert!(v.len() == 256);

    v
}

struct Chunk {
    bits: [Bit; 64]
}

impl Clone for Chunk {
    fn clone(&self) -> Chunk {
        let mut new_chunk = Chunk::from(0);

        for i in 0..64 {
            new_chunk.bits[i] = self.bits[i].clone();
        }

        new_chunk
    }
}

impl Chunk {
    fn xor(&self, other: &Chunk) -> Chunk {
        let mut new_chunk = Chunk::from(0);

        for i in 0..64 {
            new_chunk.bits[i] = self.bits[i].xor(&other.bits[i]);
        }

        new_chunk
    }

    fn notand(&self, other: &Chunk) -> Chunk {
        let mut new_chunk = Chunk::from(0);

        for i in 0..64 {
            new_chunk.bits[i] = self.bits[i].notand(&other.bits[i]);
        }

        new_chunk
    }

    fn rotl(&self, by: usize) -> Chunk {
        assert!(by < 64);
        let mut new_bits = vec![];

        new_bits.extend_from_slice(&self.bits[by..]);
        new_bits.extend_from_slice(&self.bits[0..by]);

        let mut clone = self.clone();
        clone.bits.clone_from_slice(&new_bits);

        clone
    }
}

impl PartialEq for Chunk {
    fn eq(&self, other: &Chunk) -> bool {
        for (a, b) in self.bits.iter().zip(other.bits.iter()) {
            if a != b { return false; }
        }

        true
    }
}

impl<'a> From<&'a [[Bit; 8]]> for Chunk {
    fn from(bytes: &'a [[Bit; 8]]) -> Chunk {
        assert!(bytes.len() == 8); // must be 64 bit

        let mut new_chunk = Chunk::from(0);

        for (i, byte) in bytes.iter().rev().enumerate() {
            for (j, bit) in byte.iter().enumerate() {
                new_chunk.bits[i*8 + j] = bit.clone();
            }
        }

        new_chunk
    }
}

impl<'a> From<&'a [Bit]> for Chunk {
    fn from(bits: &'a [Bit]) -> Chunk {
        assert!(bits.len() == 64); // must be 64 bit

        let mut new_chunk = Chunk::from(0);

        for (i, bit) in bits.iter().enumerate() {
            new_chunk.bits[i] = bit.clone();
        }

        new_chunk
    }
}

impl From<u64> for Chunk {
    fn from(num: u64) -> Chunk {
        use std::mem;

        fn bit_at(num: u64, i: usize) -> u8 {
            ((num << i) >> 63) as u8
        }

        // TODO: initialize this with unsafe { }
        //       sadly... GET INTEGER GENERICS WORKING RUST
        Chunk {
            bits: [
                Bit::constant(bit_at(num, 0)),
                Bit::constant(bit_at(num, 1)),
                Bit::constant(bit_at(num, 2)),
                Bit::constant(bit_at(num, 3)),
                Bit::constant(bit_at(num, 4)),
                Bit::constant(bit_at(num, 5)),
                Bit::constant(bit_at(num, 6)),
                Bit::constant(bit_at(num, 7)),
                Bit::constant(bit_at(num, 8)),
                Bit::constant(bit_at(num, 9)),
                Bit::constant(bit_at(num, 10)),
                Bit::constant(bit_at(num, 11)),
                Bit::constant(bit_at(num, 12)),
                Bit::constant(bit_at(num, 13)),
                Bit::constant(bit_at(num, 14)),
                Bit::constant(bit_at(num, 15)),
                Bit::constant(bit_at(num, 16)),
                Bit::constant(bit_at(num, 17)),
                Bit::constant(bit_at(num, 18)),
                Bit::constant(bit_at(num, 19)),
                Bit::constant(bit_at(num, 20)),
                Bit::constant(bit_at(num, 21)),
                Bit::constant(bit_at(num, 22)),
                Bit::constant(bit_at(num, 23)),
                Bit::constant(bit_at(num, 24)),
                Bit::constant(bit_at(num, 25)),
                Bit::constant(bit_at(num, 26)),
                Bit::constant(bit_at(num, 27)),
                Bit::constant(bit_at(num, 28)),
                Bit::constant(bit_at(num, 29)),
                Bit::constant(bit_at(num, 30)),
                Bit::constant(bit_at(num, 31)),
                Bit::constant(bit_at(num, 32)),
                Bit::constant(bit_at(num, 33)),
                Bit::constant(bit_at(num, 34)),
                Bit::constant(bit_at(num, 35)),
                Bit::constant(bit_at(num, 36)),
                Bit::constant(bit_at(num, 37)),
                Bit::constant(bit_at(num, 38)),
                Bit::constant(bit_at(num, 39)),
                Bit::constant(bit_at(num, 40)),
                Bit::constant(bit_at(num, 41)),
                Bit::constant(bit_at(num, 42)),
                Bit::constant(bit_at(num, 43)),
                Bit::constant(bit_at(num, 44)),
                Bit::constant(bit_at(num, 45)),
                Bit::constant(bit_at(num, 46)),
                Bit::constant(bit_at(num, 47)),
                Bit::constant(bit_at(num, 48)),
                Bit::constant(bit_at(num, 49)),
                Bit::constant(bit_at(num, 50)),
                Bit::constant(bit_at(num, 51)),
                Bit::constant(bit_at(num, 52)),
                Bit::constant(bit_at(num, 53)),
                Bit::constant(bit_at(num, 54)),
                Bit::constant(bit_at(num, 55)),
                Bit::constant(bit_at(num, 56)),
                Bit::constant(bit_at(num, 57)),
                Bit::constant(bit_at(num, 58)),
                Bit::constant(bit_at(num, 59)),
                Bit::constant(bit_at(num, 60)),
                Bit::constant(bit_at(num, 61)),
                Bit::constant(bit_at(num, 62)),
                Bit::constant(bit_at(num, 63))
            ]
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
enum Bit {
    Constant(u8)
}

impl Bit {
    fn byte(byte: u8) -> [Bit; 8] {
        [
            Bit::constant({if byte & 0b10000000 != 0 { 1 } else { 0 }}),
            Bit::constant({if byte & 0b01000000 != 0 { 1 } else { 0 }}),
            Bit::constant({if byte & 0b00100000 != 0 { 1 } else { 0 }}),
            Bit::constant({if byte & 0b00010000 != 0 { 1 } else { 0 }}),
            Bit::constant({if byte & 0b00001000 != 0 { 1 } else { 0 }}),
            Bit::constant({if byte & 0b00000100 != 0 { 1 } else { 0 }}),
            Bit::constant({if byte & 0b00000010 != 0 { 1 } else { 0 }}),
            Bit::constant({if byte & 0b00000001 != 0 { 1 } else { 0 }}),
        ]
    }

    fn constant(num: u8) -> Bit {
        assert_eq!((1 - num) * num, 0); // haha

        Bit::Constant(num)
    }

    // self xor other
    fn xor(&self, other: &Bit) -> Bit {
        match (self, other) {
            (&Bit::Constant(a), &Bit::Constant(b)) => {
                Bit::constant(a ^ b)
            },
            //_ => unimplemented!()
        }
    }

    // (not self) and other
    fn notand(&self, other: &Bit) -> Bit {
        match (self, other) {
            (&Bit::Constant(a), &Bit::Constant(b)) => {
                Bit::constant((a ^ 1) & b)
            },
            //_ => unimplemented!()
        }
    }
}

#[test]
fn testsha3() {
    let bb = |x: usize| {
        match x % 5 {
            0 => Bit::byte(0xBB),
            1 => Bit::byte(0x3B),
            2 => Bit::byte(0x1B),
            3 => Bit::byte(0x0B),
            4 => Bit::byte(0xFF),
            _ => unreachable!()
        }
    };

    let msg: Vec<_> = (0..144).map(bb).collect();

    let result = keccak256(&msg);

    let correct_result: [u64; 4] = 
                         [0x6746c5f4559bc1dd,
                          0x49d08e1adcf3be12,
                          0x80a2fcca8ce98789,
                          0x659f40a0053e2989
                         ];

    for i in 0..4 {
        let j = i * 64;
        let ours = Chunk::from(&result[j..(j+64)]);
        let correct = Chunk::from(correct_result[i]);

        assert!(ours == correct);
    }
}

#[test]
fn testff() {
    let mut a: [Chunk; 25] =
    [
        Chunk::from(0xABCDEF0123456789),
        Chunk::from(0x9ABCDEF012345678),
        Chunk::from(0x89ABCDEF01234567),
        Chunk::from(0x789ABCDEF0123456),
        Chunk::from(0x6789ABCDEF012345),
        Chunk::from(0x56789ABCDEF01234),
        Chunk::from(0x456789ABCDEF0123),
        Chunk::from(0x3456789ABCDEF012),
        Chunk::from(0x23456789ABCDEF01),
        Chunk::from(0x123456789ABCDEF0),
        Chunk::from(0x0123456789ABCDEF),
        Chunk::from(0xF0123456789ABCDE),
        Chunk::from(0xEF0123456789ABCD),
        Chunk::from(0xDEF0123456789ABC),
        Chunk::from(0xCDEF0123456789AB),
        Chunk::from(0xBCDEF0123456789A),
        Chunk::from(0xABCDEF0123456789),
        Chunk::from(0x9ABCDEF012345678),
        Chunk::from(0x89ABCDEF01234567),
        Chunk::from(0x789ABCDEF0123456),
        Chunk::from(0x6789ABCDEF012345),
        Chunk::from(0x56789ABCDEF01234),
        Chunk::from(0x456789ABCDEF0123),
        Chunk::from(0x3456789ABCDEF012),
        Chunk::from(0x23456789ABCDEF01)
    ];

    keccakf(&mut a, 24);
    /*
    ebf3844f878a7d3b
    4c9a23df85c470ef
    4c2e69353217ca2b
    a3ffa213a668ba9d
    34082fa7dc4c944b
    b8bd0a4331665932
    bfcee841052def2d
    09e2f6993a65ac0b
    ec78b15ef42a11e6
    5088c480e6a77eb8
    9c1ff840c7758823
    df8f367ad977a6b1
    517b9c3505b4195a
    04624d3094c46c2c
    e71674d1b70748e2
    6739a678e25ae9f4
    2e64f74a9528d091
    9c17a1105709cbfe
    54678a20a3ac5925
    0297df877fa4a559
    f55ec61b328a5cc5
    56637274c0f2c301
    33943408ffd9b9c5
    f4b87c711ed56d77
    3300e5d2414b6a93
    */
    assert!(a[0] == Chunk::from(0xebf3844f878a7d3b));
    assert!(a[1] == Chunk::from(0x4c9a23df85c470ef));
    assert!(a[2] == Chunk::from(0x4c2e69353217ca2b));
    assert!(a[3] == Chunk::from(0xa3ffa213a668ba9d));
    assert!(a[24] == Chunk::from(0x3300e5d2414b6a93));
}