use crate::redshift::IOP::hashes::rescue::Rescue;
use crate::pairing::ff::{PrimeField, PrimeFieldRepr};
use byteorder::{BigEndian, ReadBytesExt};
use super::Channel;
use std::convert;


#[derive(Clone)]
pub struct StatelessRescueChannel<F: PrimeField> {
    state: Rescue<F>,
    _marker: std::marker::PhantomData<F>
}

impl<F> StatelessRescueChannel<F>
where F: PrimeField {
    const SHAVE_BITS: u32 = 256 - F::CAPACITY;
    // const REPR_SIZE: usize = std::mem::size_of::<F::Repr>();
    const REP_SIZE: usize = (((F::NUM_BITS as usize)/ 64) + 1) * 8;
}

impl<F> Channel<F> for StatelessRescueChannel<F>
where F: PrimeField {
    type Input = F;

    fn new() -> Self {
        assert!(F::NUM_BITS < 256);
        Self {
            state: Rescue::default(),
            _marker: std::marker::PhantomData
        }
    }

    fn consume(&mut self, element: &Self::Input) {      
        self.state.absorb(element.clone());
    }

    fn produce_field_element_challenge(&mut self) -> F {
        let value = self.state.squeeze();
        //self.state.absorb(value.clone());
        value
    }

    fn produce_uint_challenge(&mut self) -> u64 {
        let res = if Self::REP_SIZE < 8 {
            let mut res = Vec::with_capacity(8);
            for o in res.chunks_mut(Self::REP_SIZE) {
                let element = self.state.squeeze();
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
            let element = self.state.squeeze();
            let repr = element.into_repr();
            let slice: &[u64] = repr.as_ref();
            slice[0]
        };

        res
    }
}