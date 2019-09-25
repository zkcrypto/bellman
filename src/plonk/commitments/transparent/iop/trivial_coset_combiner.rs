use crate::pairing::ff::PrimeField;
use super::*;

#[derive(Copy, Clone)]
pub struct CosetOfSizeTwo;

impl CosetInformation for CosetOfSizeTwo {
    const COSET_SIZE: usize = 2usize;
}

pub struct TrivialCombiner<F: PrimeField> {
    _marker: std::marker::PhantomData<F>
}

impl<'c, F: PrimeField> CosetCombiner<F> for TrivialCombiner<F> {
    const EXPECTED_DEGREE: usize = 2usize;
    const COSET_SIZE: usize = 2usize;

    #[inline(always)] 
    fn get_for_natural_index(leafs: &[F], natural_index: usize) -> &F {
        &leafs[natural_index]
    }

    #[inline(always)] 
    fn get_for_tree_index(leafs: &[F], tree_index: usize) -> &F {
        &leafs[tree_index]
    }

    fn get_coset_for_natural_index(natural_index: usize, domain_size: usize) -> Vec<usize> {
        assert!(natural_index < domain_size, "asking for index {} for domain size {}", natural_index, domain_size);
        let natural_pair_index = (natural_index + (domain_size / 2)) % domain_size;
        let mut coset = vec![natural_index, natural_pair_index];
        coset.sort();

        coset
    }

    fn get_coset_for_tree_index(natural_index: usize, domain_size: usize) -> Vec<usize> {
        Self::get_coset_for_natural_index(natural_index, domain_size)
    }

    #[inline(always)] 
    fn tree_index_into_natural_index(tree_index: usize) -> usize {
        tree_index
    }

    #[inline(always)] 
    fn natural_index_into_tree_index(natural_index: usize) -> usize {
        natural_index
    }    
}