use crate::pairing::ff::{Field, PrimeField, PrimeFieldRepr};
use crate::pairing::{CurveAffine, CurveProjective, Engine};
use std::io;

mod hasher;

use self::hasher::{Hasher, Keccak256Hasher, BlakeHasher};

#[derive(Clone)]
pub struct Transcript {
    transcriptor: RollingHashTranscript<Keccak256Hasher>
}

impl Transcript {
    pub fn new(personalization: &[u8]) -> Self {
        Self {
            transcriptor: RollingHashTranscript::new(personalization)
        }
    }
}

impl TranscriptProtocol for Transcript {
    fn commit_point<G: CurveAffine>(&mut self, point: &G) {
        self.transcriptor.commit_point(point);
    }

    fn commit_scalar<F: PrimeField>(&mut self, scalar: &F) {
        self.transcriptor.commit_scalar(scalar);
    }

    fn get_challenge_scalar<F: PrimeField>(&mut self) -> F {
        self.transcriptor.get_challenge_scalar()
    }
}

use std::marker::PhantomData;

#[derive(Clone)]
pub struct RollingHashTranscript<H: Hasher> {
    buffer: Vec<u8>,
    last_finalized_value: Vec<u8>,
    repeated_request_nonce: u32,
    _marker: PhantomData<H>
}

impl<H: Hasher> RollingHashTranscript<H> {
    pub fn new(personalization: &[u8]) -> Self {
        let mut h = H::new(personalization);
        let buffer = h.finalize();

        Self {
            buffer: buffer,
            last_finalized_value: vec![],
            repeated_request_nonce: 0u32,
            _marker: PhantomData
        }
    }

    pub fn commit_bytes(&mut self, personalization: &[u8], bytes: &[u8]) {
        let mut h = H::new(&[]);
        h.update(&self.buffer);
        h.update(personalization);
        h.update(bytes);

        self.buffer = h.finalize();
    }

    pub fn get_challenge_bytes(&mut self, nonce: &[u8]) -> Vec<u8> {
        let challenge_bytes = &self.buffer;

        let mut h = H::new(&[]);
        h.update(challenge_bytes);
        h.update(nonce);

        let challenge_bytes = h.finalize();

        challenge_bytes
    }
}

pub trait TranscriptProtocol {
    fn commit_point<G: CurveAffine>(&mut self, point: &G);
    fn commit_scalar<F: PrimeField>(&mut self, scalar: &F);
    fn get_challenge_scalar<F: PrimeField>(&mut self) -> F;
}

impl<H:Hasher> TranscriptProtocol for RollingHashTranscript<H> {
    fn commit_point<G: CurveAffine>(&mut self, point: &G) {
        self.commit_bytes(b"point", point.into_uncompressed().as_ref());
        // self.commit_bytes(b"point", point.into_compressed().as_ref());
        self.repeated_request_nonce = 0u32;
    }

    fn commit_scalar<F: PrimeField>(&mut self, scalar: &F) {
        let mut v = vec![];
        scalar.into_repr().write_be(&mut v).unwrap();
        // scalar.into_repr().write_le(&mut v).unwrap();

        self.commit_bytes(b"scalar", &v);
        self.repeated_request_nonce = 0u32;
    }

    fn get_challenge_scalar<F: PrimeField>(&mut self) -> F {
        use byteorder::ByteOrder;
        let mut nonce = self.repeated_request_nonce;
        loop {
            let mut nonce_bytes = vec![0u8; 4];
            byteorder::BigEndian::write_u32(&mut nonce_bytes, nonce);
            let mut repr: F::Repr = Default::default();
            let challenge_bytes = self.get_challenge_bytes(&nonce_bytes);
            repr.read_be(&challenge_bytes[..]).unwrap();

            if let Ok(result) = F::from_repr(repr) {
                // println!("Got a challenge {} for nonce = {}", result, nonce);
                self.repeated_request_nonce = nonce + 1u32;
                return result;
            }
            if nonce == (0xffffffff as u32) {
                panic!("can not make challenge scalar");
            }
            nonce += 1;
        }
    }
}

// struct TranscriptReader<'a, H:Hasher>(&'a mut Transcript<H>);

// impl<'a, H:Hasher> io::Read for TranscriptReader<'a, H: Hasher> {
//     fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
//         self.0.challenge_bytes(b"read", buf);

//         Ok(buf.len())
//     }
// }