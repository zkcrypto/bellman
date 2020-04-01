use blake2s_simd::{Params, State};
use crate::pairing::ff::{PrimeField, PrimeFieldRepr};
use byteorder::{BigEndian, ReadBytesExt};
use super::Channel;

// TODO: get rid of lazy static and hide hash parameters inside associated Params type 
lazy_static! {
    static ref CHANNEL_BLAKE2S_PARAMS: State = {
        Params::new()
            .hash_length(32)
            .key(b"Squeamish Ossifrage")
            .personal(b"S_Prng_F")
            .to_state()
    };
}

#[derive(Clone)]
pub struct Blake2sChannel<F: PrimeField> {
    state: State,
    _marker: std::marker::PhantomData<F>
}

impl<F: PrimeField> Blake2sChannel<F> {
    const SHAVE_BITS: u32 = 256 - F::CAPACITY;
    const REPR_SIZE: usize = (((F::NUM_BITS as usize)/ 64) + 1) * 8;
}

impl<F: PrimeField> Channel<F> for Blake2sChannel<F> {
    type Input = [u8; 32];
    type Params = ();

    fn new(params: &Self::Params) -> Self {
        assert!(F::NUM_BITS < 256);
        Self {
            state: CHANNEL_BLAKE2S_PARAMS.clone(),
            _marker: std::marker::PhantomData
        }
    }

    fn consume(&mut self, bytes: &Self::Input) {
        self.state.update(bytes);
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

    fn produce_uint_challenge(&mut self) -> u64 {
        let value = *(self.state.finalize().as_array());
        let mut slice = &value[..8];
        slice.read_u64::<BigEndian>().unwrap()
    }

    fn reset(&mut self) {
        self.state = CHANNEL_BLAKE2S_PARAMS.clone();
    }  
}

