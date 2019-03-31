extern crate tiny_keccak;
extern crate blake2_rfc;

use self::tiny_keccak::Keccak;
use self::blake2_rfc::blake2s::{Blake2s, blake2s};

pub trait Hasher {
    fn new(personalization: &[u8]) -> Self;
    fn update(&mut self, data: &[u8]);
    fn finalize(&mut self) -> Vec<u8>;
}

#[derive(Clone)]
pub struct BlakeHasher {
    h: Blake2s
}

impl Hasher for BlakeHasher {
    fn new(personalization: &[u8]) -> Self {
        let mut h = Blake2s::new(32);
        h.update(personalization);

        Self {
            h: h
        }
    }

    fn update(&mut self, data: &[u8]) {
        self.h.update(data);
    }

    fn finalize(&mut self) -> Vec<u8> {
        use std::mem;

        let new_h = Blake2s::new(32);
        let h = std::mem::replace(&mut self.h, new_h);

        let result = h.finalize();

        result.as_ref().to_vec().clone()
    }
}

#[derive(Clone)]
pub struct Keccak256Hasher {
    h: Keccak
}

impl Hasher for Keccak256Hasher {
    fn new(personalization: &[u8]) -> Self {
        let mut h = Keccak::new_keccak256();
        h.update(personalization);

        Self {
            h: h
        }
    }

    fn update(&mut self, data: &[u8]) {
        self.h.update(data);
    }

    fn finalize(&mut self) -> Vec<u8> {
        use std::mem;

        let new_h = Keccak::new_keccak256();
        let h = std::mem::replace(&mut self.h, new_h);

        let mut res: [u8; 32] = [0; 32];
        h.finalize(&mut res);

        res[..].to_vec()
    }
}