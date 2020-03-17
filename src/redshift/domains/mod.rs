use crate::pairing::ff::PrimeField;
use crate::SynthesisError;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Domain<F: PrimeField> {
    //size is always of the form 2^S
    pub size: u64,
    //S
    pub power_of_two: u64,
    // omega on the main domain (i.e. not in the coset)
    pub generator: F,
}

// TODO: with current impementation omega is many times computed
// However in most of the applications the generator of the domen is known in advance
// may be we should exploit this fact? 
impl<F: PrimeField> Domain<F> {
    pub fn new_for_size(size: u64) -> Result<Self, SynthesisError> {
        let size = size.next_power_of_two();
        let mut power_of_two = 0;
        let mut k = size;
        while k != 1 {
            k >>= 1;
            power_of_two += 1;
        }
        let max_power_of_two = F::S as u64;
        if power_of_two > max_power_of_two {
            return Err(SynthesisError::PolynomialDegreeTooLarge);
        }

        let mut generator = F::root_of_unity();
        for _ in power_of_two..max_power_of_two {
            generator.square()
        }

        Ok(Self {
            size: size,
            power_of_two: power_of_two,
            generator: generator
        })
    }
}