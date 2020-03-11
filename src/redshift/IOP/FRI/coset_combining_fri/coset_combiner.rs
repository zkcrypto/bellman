/// CosetCombiner is a helper structure designed to solve the following problem: 
/// assume we want to get the element at index [i] located in FRI oracle 
/// however the values stored in FRI oracles are permuted, so that elements of the same coset are adjacent 
/// So, we need to somehow get all elements of rhe same coset using natural index [i], i.e. 
/// make a conversion from "natural" element index to "tree" coset index
/// note, that this depends only on the number of elements in each coset i.e. "collapsing factor"

use std::ops::Range;


pub struct CosetCombiner {}
    

impl CosetCombiner {
    //wrapping factor here is size of coset: 1 << collapsing_factor
    pub fn get_coset_for_natural_index(
        natural_index: usize, 
        domain_size: usize,
        log_domain_size: usize, 
        collapsing_factor: usize) -> Range<usize> 
    {    
        assert!(natural_index < domain_size, "asking for index {} for domain size {}", natural_index, domain_size);
        assert_eq!(1 << log_domain_size, domain_size);

        let mut mask = (1 << collapsing_factor) - 1;
        mask = mask << (log_domain_size - collapsing_factor); 

        let start_idx = (natural_index & mask) << collapsing_factor;
        let coset_size = 1 << collapsing_factor;
        start_idx..(start_idx + coset_size) 
    }
}
    
