use crate::ff::PrimeField;

pub trait FftPrecomputations<F: PrimeField>: Send + Sync {
    fn new_for_domain_size(size: usize) -> Self;
    fn element_for_index(&self, index: usize) -> &F;
    fn domain_size(&self) -> usize;
}

pub(crate) mod fft;