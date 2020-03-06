use crate::pairing::ff::PrimeField;
pub mod blake_channel;
pub mod rescue_channel;

//this trait is used for implementation of Fiat-Shamir heuristics
//it is used for consuming prover's non-interactive commitments and outputing challenges
//we want the trait to be very generic, so it should be able to consume both field elements and raw bytes
//(as for example we want Channel to work with different types of hashes - 
// some of them produce raw bytes as their output, and others return field elements)
//Also the channel need to produce different types of output
//we sometimes need new field elemets as output and sometimes we do need integer in some range -
// the latter is used in FRI, when we take index of the element on the top level domain.
// However we prefer to return raw bytes in the latter case
pub trait Channel<F: PrimeField>: Sized + Clone + 'static {
    type Input;
    fn new() -> Self;
    fn consume(&mut self, data: &Self::Input);
    fn produce_field_element_challenge(&mut self) -> F;
    fn produce_challenge_bytes(&mut self, num_of_bytes: usize) -> Vec<u8>;
}





