const KECCAKF_RNDC: [u64; 24] = 
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

const KECCAKF_ROTC: [usize; 24] = 
[
    1,  3,  6,  10, 15, 21, 28, 36, 45, 55, 2,  14, 
    27, 41, 56, 8,  25, 43, 62, 18, 39, 61, 20, 44
];

const KECCAKF_PILN: [usize; 24] = 
[
    10, 7,  11, 17, 18, 3, 5,  16, 8,  21, 24, 4, 
    15, 23, 19, 13, 12, 2, 20, 14, 22, 9,  6,  1 
];

fn keccakf(st: &mut [Chunk], rounds: usize)
{
    assert_eq!(st.len(), 25);
    for round in 0..rounds {
        /*
        // Theta
        for (i = 0; i < 5; i++)     
            bc[i] = st[i] ^ st[i + 5] ^ st[i + 10] ^ st[i + 15] ^ st[i + 20];
        */

        let mut bc: Vec<Chunk> = (0..5).map(|i| st[i]
                                                .xor(&st[i+5])
                                                .xor(&st[i+10])
                                                .xor(&st[i+15])
                                                .xor(&st[i+20])
                                           ).collect();

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
                let j = KECCAKF_PILN[i];

                bc[0] = st[j].clone();
                st[j] = tmp.rotl(KECCAKF_ROTC[i]);
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

        st[0] = st[0].xor(&KECCAKF_RNDC[round].into());
    }
}

fn temporary_shim(state: &mut [Byte]) {
    assert_eq!(state.len(), 200);

    let mut chunks = Vec::with_capacity(25);
    for i in 0..25 {
        chunks.push(Chunk::from(0x0000000000000000));
    }

    for (chunk_bit, input_bit) in chunks.iter_mut().flat_map(|c| c.bits.iter_mut())
                                        .zip(state.iter().flat_map(|c| c.bits.iter()))
    {
        *chunk_bit = input_bit.clone();
    }

    keccakf(&mut chunks, 24);

    for (chunk_bit, input_bit) in chunks.iter().flat_map(|c| c.bits.iter())
                                        .zip(state.iter_mut().flat_map(|c| c.bits.iter_mut()))
    {
        *input_bit = chunk_bit.clone();
    }
}

fn sha3_256(message: &[Byte]) -> Vec<Byte> {
    keccak(1088, 512, message, 0x06, 32)
}

fn keccak(rate: usize, capacity: usize, mut input: &[Byte], delimited_suffix: u8, mut mdlen: usize)
    -> Vec<Byte>
{
    use std::cmp::min;

    let mut st: Vec<Byte> = Some(Bit::byte(0)).into_iter().cycle().take(200).collect();

    let rateInBytes = rate / 8;
    let mut inputByteLen = input.len();
    let mut blockSize = 0;

    if ((rate + capacity) != 1600) || ((rate % 8) != 0) {
        panic!("invalid parameters");
    }

    while inputByteLen > 0 {
        blockSize = min(inputByteLen, rateInBytes);

        for i in 0..blockSize {
            st[i] = st[i].xor(&input[i]);
        }

        input = &input[blockSize..];
        inputByteLen -= blockSize;

        if blockSize == rateInBytes {
            temporary_shim(&mut st);
            blockSize = 0;
        }
    }

    st[blockSize] = st[blockSize].xor(&Bit::byte(delimited_suffix));

    if ((delimited_suffix & 0x80) != 0) && (blockSize == (rateInBytes-1)) {
        temporary_shim(&mut st);
    }

    st[rateInBytes-1] = st[rateInBytes-1].xor(&Bit::byte(0x80));

    temporary_shim(&mut st);

    let mut output = Vec::with_capacity(mdlen);

    while mdlen > 0 {
        blockSize = min(mdlen, rateInBytes);
        output.extend_from_slice(&st[0..blockSize]);
        mdlen -= blockSize;

        if mdlen > 0 {
            temporary_shim(&mut st);
        }
    }

    output
}

fn keccak256(input: &[Byte]) -> Vec<Bit> {
    assert_eq!(input.len(), 144);

    let mut st: Vec<Chunk> = Some(Chunk::from(0)).into_iter().cycle().take(25).collect();

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
        let tmp: Vec<_> = st[i].bits.chunks(8)
                                    .rev()
                                    .flat_map(|x| x.iter())
                                    .map(|x| x.clone())
                                    .collect();
        v.extend_from_slice(&tmp);
    }

    assert!(v.len() == 256);

    v
}

#[derive(Clone)]
struct Chunk {
    bits: Vec<Bit>
}

impl Chunk {
    fn xor(&self, other: &Chunk) -> Chunk {
        Chunk {
            bits: self.bits.iter()
                           .zip(other.bits.iter())
                           .map(|(a, b)| a.xor(b))
                           .collect()
        }
    }

    fn notand(&self, other: &Chunk) -> Chunk {
        Chunk {
            bits: self.bits.iter()
                           .zip(other.bits.iter())
                           .map(|(a, b)| a.notand(b))
                           .collect()
        }
    }

    fn rotl(&self, mut by: usize) -> Chunk {
        by = by % 64;

        Chunk {
            bits: self.bits[by..].iter()
                                 .chain(self.bits[0..by].iter())
                                 .cloned()
                                 .collect()
        }
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

impl<'a> From<&'a [Byte]> for Chunk {
    fn from(bytes: &'a [Byte]) -> Chunk {
        assert!(bytes.len() == 8); // must be 64 bit

        Chunk {
            bits: bytes.iter().rev() // endianness
                       .flat_map(|x| x.bits.iter())
                       .cloned()
                       .collect()
        }
    }
}

impl<'a> From<&'a [Bit]> for Chunk {
    fn from(bits: &'a [Bit]) -> Chunk {
        assert!(bits.len() == 64); // must be 64 bit

        Chunk {
            bits: bits.iter().cloned().collect()
        }
    }
}

impl From<u64> for Chunk {
    fn from(num: u64) -> Chunk {
        fn bit_at(num: u64, i: usize) -> u8 {
            ((num << i) >> 63) as u8
        }

        Chunk {
            bits: (0..64).map(|i| Bit::constant(bit_at(num, i))).collect()
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
enum Bit {
    Constant(u8)
}

#[derive(Clone, Debug, PartialEq)]
struct Byte {
    bits: Vec<Bit>
}

impl Byte {
    fn grab(&self) -> u8 {
        let mut cur = 7;
        let mut acc = 0;

        for bit in &self.bits {
            if let &Bit::Constant(1) = bit {
                acc |= 0b00000001 << cur;
            }
            cur -= 1;
        }

        acc
    }

    fn xor(&self, other: &Byte) -> Byte {
        Byte {
            bits: self.bits.iter()
                           .zip(other.bits.iter())
                           .map(|(a, b)| a.xor(b))
                           .collect()
        }
    }
}

impl Bit {
    fn byte(byte: u8) -> Byte {
        Byte {
            bits: (0..8).map(|i| byte & (0b00000001 << i) != 0)
                        .map(|b| Bit::constant(if b { 1 } else { 0 }))
                        .rev()
                        .collect()
        }
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
fn test_shim() {
    let mut chunks: Vec<_> = (0..25).map(|_| Chunk::from(0xABCDEF0123456789)).collect();
    keccakf(&mut chunks, 24);

    let mut bytes: Vec<Byte> = (0..200).map(|i| {
        match i % 8 {
            0 => Bit::byte(0xAB),
            1 => Bit::byte(0xCD),
            2 => Bit::byte(0xEF),
            3 => Bit::byte(0x01),
            4 => Bit::byte(0x23),
            5 => Bit::byte(0x45),
            6 => Bit::byte(0x67),
            7 => Bit::byte(0x89),
            _ => unreachable!()
        }
    }).collect();

    temporary_shim(&mut bytes);

    for (i, bit) in bytes.iter().flat_map(|c| c.bits.iter()).enumerate() {
        //println!("i = {}", i);
        if &chunks[i / 64].bits[i % 64] != bit {
            panic!("fuck.");
        }
    }
}

#[test]
fn byte_grab_works() {
    {
        let b = Bit::byte(0xef);

        assert_eq!(0xef, b.grab());
    }
}

#[test]
fn woohoo() {
    let message = [Bit::byte(0x30)];
    let test = sha3_256(&message);

    for i in 0..32 {
        print!("{:02x} ", test[i].grab());
    }
    println!("");
    panic!("fuck");
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

    let msg: Vec<Byte> = (0..144).map(bb).collect();

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
    let base = Chunk::from(0xABCDEF0123456789);

    let mut a: Vec<Chunk> = (0..25).map(|i| base.rotl(i*4)).collect();

    keccakf(&mut a, 24);
    const TEST_VECTOR: [u64; 25] = [
        0x4c8948fcb6616044,
        0x75642a21f8bd1299,
        0xb2e949825ace668e,
        0x9b73a04c53826c35,
        0x914989b8d38ea4d1,
        0xdc73480ade4e2664,
        0x931394137c6fbd69,
        0x234fa173896019f5,
        0x906da29a7796b157,
        0x7666ebe222445610,
        0x41d77796738c884e,
        0x8861db16234437fa,
        0xf07cb925b71f27f2,
        0xfec25b4810a2202c,
        0xa8ba9bbfa9076b54,
        0x18d9b9e748d655b9,
        0xa2172c0059955be6,
        0xea602c863b7947b8,
        0xc77f9f23851bc2bd,
        0x0e8ab0a29b3fef79,
        0xfd73c2cd3b443de4,
        0x447892bf2c03c2ef,
        0xd5b3dae382c238b1,
        0x2103d8a64e9f4cb6,
        0xfe1f57d88e2de92f
    ];

    for i in 0..25 {
        assert!(a[i] == Chunk::from(TEST_VECTOR[i]));
    }
}