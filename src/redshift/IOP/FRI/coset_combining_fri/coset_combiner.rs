/// CosetCombiner is a helper structure designed to solve the following problem: 
/// assume we want to get the element at index [i] located in FRI oracle 
/// however the values stored in FRI oracles are permuted, so that elements of the same coset are adjacent 
/// So, we need to somehow get all elements of rhe same coset using natural index [i], i.e. 
/// make a conversion from "natural" element index to "tree" coset index
/// note, that this depends only on the number of elements in each coset i.e. "collapsing factor"

use std::ops::Range;
use crate::redshift::fft::cooley_tukey_ntt::bitreverse;


pub struct CosetCombiner {}
    

impl CosetCombiner {
    //wrapping factor here is size of coset: 1 << collapsing_factor
    pub fn get_coset_idx_for_natural_index(
        natural_index: usize, 
        domain_size: usize,
        log_domain_size: usize, 
        collapsing_factor: usize) -> Range<usize> 
    {    
        assert!(natural_index < domain_size, "asking for index {} for domain size {}", natural_index, domain_size);
        assert_eq!(1 << log_domain_size, domain_size);

        let mut mask = (1 << collapsing_factor) - 1;
        mask = !(mask << (log_domain_size - collapsing_factor)); 

        let start_idx = (natural_index & mask) << collapsing_factor;
        let coset_size = 1 << collapsing_factor;
        start_idx..(start_idx + coset_size) 
    }

    //do the same as get_coset, but also return the tree index of the current element
    pub fn get_coset_idx_for_natural_index_extended(
        natural_index: usize, 
        domain_size: usize,
        log_domain_size: usize, 
        collapsing_factor: usize) -> (Range<usize>, usize)
    {
        assert!(natural_index < domain_size, "asking for index {} for domain size {}", natural_index, domain_size);
        assert_eq!(1 << log_domain_size, domain_size);

        let endpoint_mask = (1 << collapsing_factor) - 1;
        let mask = !(endpoint_mask << (log_domain_size - collapsing_factor)); 

        let start_idx = (natural_index & mask) << collapsing_factor;
        let coset_size = 1 << collapsing_factor;
        let coset_idx_range = start_idx..(start_idx + coset_size);
        
        // NB: shift should be bitreversed
        let shift = bitreverse(natural_index, log_domain_size as usize) & endpoint_mask;
        (coset_idx_range, start_idx + shift)
    }

    pub fn get_natural_idx_for_coset_index(
        coset_index: usize,
        domain_size: usize,
        log_domain_size: usize,
        collapsing_factor: usize) -> usize
    {
        assert!(coset_index < domain_size, "asking for index {} for domain size {}", coset_index, domain_size);
        assert_eq!(1 << log_domain_size, domain_size);

        let start_idx = coset_index >> collapsing_factor;
        let mask = (1 << collapsing_factor) - 1;
        let shift = bitreverse(coset_index & mask, log_domain_size as usize);
        mask + shift
    }
}


#[cfg(test)]
mod test {
    #[test]
    fn test_coset_combiner() {
        use super::*;
        let domain_size = 2u32.pow(16) as usize;
        let log_domain_size = 16;
        let collapsing_factor = 4;

        let natural_index = 837;
        let (_coset_idx_range, coset_idx) = CosetCombiner::get_coset_idx_for_natural_index_extended(
            natural_index, domain_size, log_domain_size, collapsing_factor);
        assert_eq!(natural_index, CosetCombiner::get_natural_idx_for_coset_index(
            coset_idx, domain_size, log_domain_size, collapsing_factor));

        let coset_index = 23;
        let natural_idx = CosetCombiner::get_natural_idx_for_coset_index(
            coset_index, domain_size, log_domain_size, collapsing_factor);
        assert_eq!(coset_idx, CosetCombiner::get_coset_idx_for_natural_index_extended(
            natural_idx, domain_size, log_domain_size, collapsing_factor).1);
    }
}
    
