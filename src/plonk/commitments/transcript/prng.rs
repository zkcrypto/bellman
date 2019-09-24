use blake2s_simd::{Params, State};
use crate::pairing::ff::{PrimeField, PrimeFieldRepr};
use super::Prng;

lazy_static! {
    static ref STATELESS_PRNG_BLAKE2S_PARAMS: State = {
        Params::new()
            .hash_length(32)
            .key(b"Squeamish Ossifrage")
            .personal(b"S_Prng_F")
            .to_state()
    };
}

#[derive(Clone)]
pub struct StatelessBlake2sPrng<F: PrimeField> {
    state: State,
    _marker: std::marker::PhantomData<F>
}

impl<F: PrimeField> StatelessBlake2sPrng<F> {
    const SHAVE_BITS: u32 = 256 - F::CAPACITY;
    const REPR_SIZE: usize = std::mem::size_of::<F::Repr>();
}

impl<F: PrimeField> Prng<F> for StatelessBlake2sPrng<F> {
    type Input = F;

    fn new() -> Self {
        assert!(F::NUM_BITS < 256);
        Self {
            state: STATELESS_PRNG_BLAKE2S_PARAMS.clone(),
            _marker: std::marker::PhantomData
        }
    }

    fn commit_input(&mut self, input: &Self::Input) {
        let mut state = STATELESS_PRNG_BLAKE2S_PARAMS.clone();
        let repr = input.into_repr();
        let mut bytes: Vec<u8> = vec![0u8; Self::REPR_SIZE];
        repr.write_be(&mut bytes[..]).expect("should write");
        state.update(&bytes[..]);
        self.state = state;
    }

    fn get_challenge(&mut self) -> F {
        let value = *(self.state.finalize().as_array());
        self.state = STATELESS_PRNG_BLAKE2S_PARAMS.clone();
        
        let mut repr = F::Repr::default();
        let shaving_mask: u64 = 0xffffffffffffffff >> (Self::SHAVE_BITS % 64);
        repr.read_be(&value[..]).expect("will read");
        let last_limb_idx = repr.as_ref().len() - 1;
        repr.as_mut()[last_limb_idx] &= shaving_mask;
        let value = F::from_repr(repr).expect("in a field");

        value
    }
}
