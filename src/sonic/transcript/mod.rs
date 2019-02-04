extern crate ff;
extern crate pairing;

use ff::{Field, PrimeField, PrimeFieldRepr};
use pairing::{CurveAffine, CurveProjective, Engine};
use std::io;

// transcript is mocked for now
#[derive(Clone)]
pub struct Transcript {
    buffer: Vec<u8>
}

impl Transcript {
    pub fn new(personalization: &[u8]) -> Self {
        Self {
            buffer: vec![]
        }
    }

    pub fn commit_bytes(&mut self, personalization: &[u8], bytes: &[u8]) {

    }

    pub fn challenge_bytes(&mut self, personalization: &[u8], bytes: &[u8]) {

    }
}

pub trait TranscriptProtocol {
    fn commit_point<G: CurveAffine>(&mut self, point: &G);
    fn commit_scalar<F: PrimeField>(&mut self, scalar: &F);
    fn get_challenge_scalar<F: PrimeField>(&mut self) -> F;
}

impl TranscriptProtocol for Transcript {
    fn commit_point<G: CurveAffine>(&mut self, point: &G) {
        self.commit_bytes(b"point", point.into_compressed().as_ref());
    }

    fn commit_scalar<F: PrimeField>(&mut self, scalar: &F) {
        let mut v = vec![];
        scalar.into_repr().write_le(&mut v).unwrap();

        self.commit_bytes(b"scalar", &v);
    }

    fn get_challenge_scalar<F: PrimeField>(&mut self) -> F {
        return F::one();
        // loop {
        //     let mut repr: F::Repr = Default::default();
        //     repr.read_be(TranscriptReader(self)).unwrap();

        //     if let Ok(result) = F::from_repr(repr) {
        //         return result;
        //     }
        // }
    }
}

struct TranscriptReader<'a>(&'a mut Transcript);

impl<'a> io::Read for TranscriptReader<'a> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.0.challenge_bytes(b"read", buf);

        Ok(buf.len())
    }
}