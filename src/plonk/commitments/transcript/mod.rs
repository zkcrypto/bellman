use blake2s_simd::{Params, State};
use crate::pairing::ff::{PrimeField, PrimeFieldRepr};

pub mod prng;

lazy_static! {
    static ref TRANSCRIPT_BLAKE2S_PARAMS: State = {
        Params::new()
            .hash_length(32)
            .key(b"Squeamish Ossifrage")
            .personal(b"Shaftoe")
            .to_state()
    };
}

pub trait Prng<F: PrimeField>: Sized + Clone + 'static {
    type Input;
    fn new() -> Self;
    fn commit_input(&mut self, input: &Self::Input);
    fn get_challenge(&mut self) -> F;
}

pub trait Transcript<F: PrimeField>: Prng<F> + Sized + Clone + 'static {
    fn commit_bytes(&mut self, bytes: &[u8]);
    fn commit_field_element(&mut self, element: &F);
    fn get_challenge_bytes(&mut self) -> Vec<u8>;
}

#[derive(Clone)]
pub struct Blake2sTranscript<F: PrimeField> {
    state: State,
    _marker: std::marker::PhantomData<F>
}

impl<F: PrimeField> Blake2sTranscript<F> {
    const SHAVE_BITS: u32 = 256 - F::CAPACITY;
    const REPR_SIZE: usize = std::mem::size_of::<F::Repr>();
}


// impl<F: PrimeField> Prng<F> for Blake2sTranscript<F> {
//     type Input = F;

//     fn new() -> Self {
//         assert!(F::NUM_BITS < 256);
//         let state = (*TRANSCRIPT_BLAKE2S_PARAMS).clone();
//         Self {
//             state,
//             _marker: std::marker::PhantomData
//         }
//     }

//     fn commit_input(&mut self, input: &Self::Input) {
//         self.commit_field_element(input)
//     }

//     fn get_challenge(&mut self) -> F {
//         let value = *(self.state.finalize().as_array());
//         self.state.update(&value[..]);
        
//         let mut repr = F::Repr::default();
//         let shaving_mask: u64 = 0xffffffffffffffff >> (Self::SHAVE_BITS % 64);
//         repr.read_be(&value[..]).expect("will read");
//         let last_limb_idx = repr.as_ref().len() - 1;
//         repr.as_mut()[last_limb_idx] &= shaving_mask;
//         let value = F::from_repr(repr).expect("in a field");

//         value
//     }
// }

impl<F: PrimeField> Prng<F> for Blake2sTranscript<F> {
    type Input = [u8; 32];

    fn new() -> Self {
        assert!(F::NUM_BITS < 256);
        let state = (*TRANSCRIPT_BLAKE2S_PARAMS).clone();
        Self {
            state,
            _marker: std::marker::PhantomData
        }
    }

    fn commit_input(&mut self, input: &Self::Input) {
        self.commit_bytes(input)
    }

    fn get_challenge(&mut self) -> F {
        let value = *(self.state.finalize().as_array());
        self.state.update(&value[..]);
        
        let mut repr = F::Repr::default();
        let shaving_mask: u64 = 0xffffffffffffffff >> (Self::SHAVE_BITS % 64);
        repr.read_be(&value[..]).expect("will read");
        let last_limb_idx = repr.as_ref().len() - 1;
        repr.as_mut()[last_limb_idx] &= shaving_mask;
        let value = F::from_repr(repr).expect("in a field");

        value
    }
}

impl<F: PrimeField> Transcript<F> for Blake2sTranscript<F> {
    fn commit_bytes(&mut self, bytes: &[u8]) {
        self.state.update(&bytes);
    }

    fn commit_field_element(&mut self, element: &F) {
        let repr = element.into_repr();
        let mut bytes: Vec<u8> = vec![0u8; Self::REPR_SIZE];
        repr.write_be(&mut bytes[..]).expect("should write");
        self.state.update(&bytes[..]);
    }

    fn get_challenge_bytes(&mut self) -> Vec<u8> {
        let value = *(self.state.finalize().as_array());
        self.state.update(&value[..]);

        Vec::from(&value[..])
    }
}
