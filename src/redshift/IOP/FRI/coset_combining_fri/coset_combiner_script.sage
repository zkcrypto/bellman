domain_size = 32
wrapping_factor = 1


def log2(num):
    assert (num & (num-1) == 0) and num != 0, "%d is not a power of two" % num
    
    pow =  0

    while (1 << (pow+1)) <= num :
        pow += 1
    return pow


def bitreverse(num, limit):
    initial_num = num
    initial_limit = limit
    
    result = 0
    while limit:
        result = (result << 1) + (num & 1)
        num >>= 1
        limit -= 1
    
    assert num == 0, "%d contains more than %d bits" % (initial_num, initial_limit) 
    return result


def combine_in_cosets(domain_size, wrapping_factor):
    res = []
    log_domain_size = log2(domain_size)
    
    collapsing_factor = 1 << wrapping_factor
    for i in xrange(domain_size / collapsing_factor):
        for j in xrange(collapsing_factor):
            res.append(i + bitreverse(j, log_domain_size))
        
    return res


def get_coset_idx_for_natural_index(natural_index, domain_size, collapsing_factor):
    
    log_domain_size = log2(domain_size)
    mask = (1 << collapsing_factor) - 1;
    mask = ~int(mask << (log_domain_size - collapsing_factor)); 

    start_idx = (natural_index & mask) << collapsing_factor;
    coset_size = 1 << collapsing_factor;
    return tuple(range(start_idx, (start_idx + coset_size)))


def get_coset_idx_for_natural_index_extended(natural_index, domain_size, collapsing_factor):
    
    log_domain_size = log2(domain_size)
    
    endpoint_mask = (1 << collapsing_factor) - 1;
    mask = ~int(endpoint_mask << (log_domain_size - collapsing_factor)); 

    start_idx = (natural_index & mask) << collapsing_factor;
    coset_size = 1 << collapsing_factor;
    coset_idx_range = tuple(range(start_idx,(start_idx + coset_size)));

    # NB: shift should be bitreversed
    shift = bitreverse(natural_index, log_domain_size) & endpoint_mask;
    return (coset_idx_range, start_idx + shift)


def get_natural_idx_for_coset_index(coset_index, domain_size, collapsing_factor):
    
    log_domain_size = log2(domain_size)
    
    endpoint_mask = (1 << collapsing_factor) - 1;
    
    start_idx = coset_index >> collapsing_factor;
    mask = (1 << collapsing_factor) - 1;
    shift = bitreverse(coset_index & mask, log_domain_size);
    return mask + shift


print combine_in_cosets(16, 2)

domain_size = 32
wrapping_factor = 1

print get_coset_idx_for_natural_index_extended(5, 16, 2)
print get_coset_idx_for_natural_index_extended(10 % 8, 8, 2)


#print get_natural_idx_for_coset_index(1, 16, 2)