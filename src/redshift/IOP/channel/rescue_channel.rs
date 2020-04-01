use crate::redshift::IOP::hashes::rescue::{Rescue, RescueParams};
use crate::pairing::ff::{PrimeField, PrimeFieldRepr};
use byteorder::{BigEndian, ReadBytesExt};
use super::Channel;
use std::convert;


pub struct RescueChannel<'a, F: PrimeField, RP: RescueParams<F>> {
    state: Rescue<F, RP>,
    params: &'a RP,
}

pub struct RescueChannelParams<'a, F: PrimeField, RP: RescueParams<F>> {
    pub rescue_params: &'a RP,
    pub _marker: std::marker::PhantomData<F>
}

impl<'a, F, RP> RescueChannel<'a, F, RP>
where F: PrimeField, RP: RescueParams<F> {
    const SHAVE_BITS: u32 = 256 - F::CAPACITY;
    // const REPR_SIZE: usize = std::mem::size_of::<F::Repr>();
    const REP_SIZE: usize = (((F::NUM_BITS as usize)/ 64) + 1) * 8;
}

impl<'a, F, RP> Channel<F> for RescueChannel<'a, F, RP>
where F: PrimeField, RP: RescueParams<F> {
    type Input = F;
    type Params = RescueChannelParams<'a, F, RP>;

    fn new(channel_params: &Self::Params) -> Self {
        assert!(F::NUM_BITS < 256);
        Self {
            state: Rescue::new(channel_params.rescue_params),
            params: channel_params.rescue_params,
        }
    }

    fn consume(&mut self, element: &Self::Input) {      
        self.state.absorb(element.clone(), self.params);
    }

    fn produce_field_element_challenge(&mut self) -> F {
        self.state.squeeze(self.params)
    }

    fn produce_uint_challenge(&mut self) -> u64 {
        let res = if Self::REP_SIZE < 8 {
            let mut res = Vec::with_capacity(8);
            for o in res.chunks_mut(Self::REP_SIZE) {
                let element = self.state.squeeze(self.params);
                // TODO: do we really need to absorb here?
                //self.state.absorb(element.clone());

                let repr = element.into_repr();
                if o.len() == Self::REP_SIZE {
                    repr.write_be(o).expect("should write");       
                }
                else {
                    //because rust sucks!
                    let mut scratch_space = [0u8; 32];
                    repr.write_be(& mut scratch_space[..]).expect("should write");  
                    o.copy_from_slice(&scratch_space[0..o.len()]);  
                }
            }
            let mut slice = &res[..8];
            slice.read_u64::<BigEndian>().unwrap()
        }
        else {
            let element = self.state.squeeze(self.params);
            let repr = element.into_repr();
            let slice: &[u64] = repr.as_ref();
            slice[0]
        };

        res
    }

    fn reset(&mut self) {
        self.state.clear_state();
    }
}