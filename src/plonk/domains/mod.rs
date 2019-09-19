use crate::pairing::ff::PrimeField;
use crate::SynthesisError;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Domain<F: PrimeField> {
    pub size: u64,
    pub power_of_two: u64,
    pub generator: F,
}

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