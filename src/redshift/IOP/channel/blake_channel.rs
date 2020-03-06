use blake2s_simd::{Params, State};
use crate::pairing::ff::{PrimeField, PrimeFieldRepr};
use super::Channel;


lazy_static! {
    static ref STATELESS_CHANNEL_BLAKE2S_PARAMS: State = {
        Params::new()
            .hash_length(32)
            .key(b"Squeamish Ossifrage")
            .personal(b"S_Prng_F")
            .to_state()
    };
}

#[derive(Clone)]
pub struct StatelessBlake2sChannel<F: PrimeField> {
    state: State,
    _marker: std::marker::PhantomData<F>
}

impl<F: PrimeField> StatelessBlake2sChannel<F> {
    const SHAVE_BITS: u32 = 256 - F::CAPACITY;
    // const REPR_SIZE: usize = std::mem::size_of::<F::Repr>();
    const REPR_SIZE: usize = (((F::NUM_BITS as usize)/ 64) + 1) * 8;
}

impl<F: PrimeField> Channel<F> for StatelessBlake2sChannel<F> {
    type Input = [u8; 32];

    fn new() -> Self {
        assert!(F::NUM_BITS < 256);
        Self {
            state: STATELESS_CHANNEL_BLAKE2S_PARAMS.clone(),
            _marker: std::marker::PhantomData
        }
    }

    fn consume(&mut self, bytes: &Self::Input) {
        self.state.update(&bytes);
    }

    fn produce_field_element_challenge(&mut self) -> F {
        let value = *(self.state.finalize().as_array());
        
        let mut repr = F::Repr::default();
        let shaving_mask: u64 = 0xffffffffffffffff >> (Self::SHAVE_BITS % 64);
        repr.read_be(&value[..]).expect("will read");
        let last_limb_idx = repr.as_ref().len() - 1;
        repr.as_mut()[last_limb_idx] &= shaving_mask;
        let value = F::from_repr(repr).expect("in a field");

        value
    }

    fn produce_challenge_bytes(&mut self, num_of_bytes: usize) -> Vec<u8> {
        let mut res = Vec::with_capacity(num_of_bytes);
        let hash_length = 32;
        
        for o in res.chunks_mut(hash_length) {
            let value = *(self.state.finalize().as_array());

            self.state.update(&value[..]);
            o.copy_from_slice(&value[0..o.len()]);
        }

        res
    }    
}

