c = 1
r = 2
num_rounds = 22
p = 21888242871839275222246405745257275088548364400416034343698204186575808495617
field = GF(p)
#generator of multiplicative subgroup
g = field(7)
IV = "RESCUE"



def generate_round_constant(fn_name, field, idx):
    """
    Returns a field element based on the result of sha256.
    The input to sha256 is the concatenation of the name of the hash function
    and an index.
    For example, the first element for MiMC will be computed using the value
    of sha256('MiMC0').
    """
    from hashlib import sha256
    val = int(sha256('%s%d' % (fn_name, idx)).hexdigest(), 16)
    return field(val)
    

def generate_mds_matrix(name, field, m, num_attempts = 100):
    """
    Generates an MDS matrix of size m x m over the given field, with no
    eigenvalues in the field.
    Given two disjoint sets of size m: {x_1, ..., x_m}, {y_1, ..., y_m} we set
    A_{ij} = 1 / (x_i - y_j).
    """
    for attempt in xrange(100):
        x_values = [generate_round_constant(name + 'x', field, attempt * m + i)
                    for i in xrange(m)]
        y_values = [generate_round_constant(name + 'y', field, attempt * m + i)
                    for i in xrange(m)]
        
        # Make sure the values are distinct.
        if len(set(x_values + y_values)) != 2 * m:
            continue
        mds = matrix([[1 / (x_values[i] - y_values[j]) for j in xrange(m)]
                      for i in xrange(m)])
        
        if len(mds.characteristic_polynomial().roots()) == 0:
            # There are no eigenvalues in the field.
            return mds
    raise Exception('No good MDS found')
                                            
                                            
def generate_round_parameters(field, r, c, num_rounds, iv):
    
    m = r + c                                           
    assert c <= r
    MDS = generate_mds_matrix(IV + "MDS", field, m)
    round_constants = [
        vector(generate_round_constant(IV + "K", field, m * i + j) for j in xrange(m)) for i in xrange(2 * num_rounds + 1)]
    
    return MDS, round_constants


def find_rescue_alpha_inalpha(p):
    
    # RESCUE_ALPHA : Ideally the smallest prime such that gcd(p - 1, RESCUE_ALPHA) = 1
    # RESCUE_INVALPHA * RESCUE_ALPHA = 1 mod (p - 1) 
    temp = 3
    while True:
        d,u,v = xgcd(p-1, temp)
        if d == 1:
            alpha = temp
            inalpha = v % (p-1)
            return alpha, inalpha
        
        temp += 2
            

def generate_rescue_field_parameters(field):
    
    p = field.cardinality()
    
    # p - 1 is divisible by 2^s and not divisible by 2^(s+1)
    s = 0
    temp = p - 1
    while not (temp & 1):
        s += 1
        temp >>= 1
    
    # Generator of the 2^s multiplicative subgroup
    # equals g ^ (p-1/{2^s})
    alpha = g ^ ((p-1) / (2^s))
    
    rescue_alpha, rescue_inalpha = find_rescue_alpha_inalpha(p)
    
    
    return s, alpha, rescue_alpha, rescue_inalpha


s, alpha, rescue_alpha, rescue_inalpha = generate_rescue_field_parameters(field)

print "s: ", s
print "alpha: ", alpha
print "rescue_alpha: ", rescue_alpha
print "rescue_inalpha: ", rescue_inalpha,
print "hexed rescue_inalpha: ", hex(rescue_inalpha)

"representation of inalpha by array of u64: "
temp = rescue_inalpha
res = []
for _ in xrange(4):
    res.append(temp % 2^64)
    temp >>= 64
print temp
print res


                                            
MDS, round_constants = generate_round_parameters(field, r, c, num_rounds, IV)

print "MDS: "
print MDS

for (i, round) in enumerate(round_constants):
    for idx, elem in enumerate(round):
        if idx == 0:
            print "[\"" + str(elem) + "\", "
        elif idx == (r+c-1):
            print " \"" + str(elem) + "\"],\n"
        else:
            print " \"" + str(elem) + "\", "