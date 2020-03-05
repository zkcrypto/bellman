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

    pub fn coset_for_natural_index_and_size(natural_index: usize, domain_size: usize) -> Vec<usize> {
        assert!(domain_size > 1);
        assert!(domain_size.is_power_of_two());
        let natural_pair_index = (natural_index + (domain_size / 2)) % domain_size;
        let mut coset = vec![natural_index, natural_pair_index];
        coset.sort();

        coset
    }

    pub fn index_and_size_for_next_domain(natural_index: usize, domain_size: usize) -> (usize, usize) {
        // maps coset index into element of the next domain
        // if index < current_size / 2 -> return index
        // else -> return index - current_size / 2
        assert!(domain_size > 1);
        assert!(domain_size.is_power_of_two());
        let next_size = domain_size / 2;

        let next_index = if natural_index < next_size {
            natural_index
        } else {
            natural_index - next_size
        };

        (next_index, next_size)
    }
}