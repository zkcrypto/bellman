use curves::{Engine, Field, SnarkField, PrimeField, Group};

pub struct EvaluationDomain<E: Engine> {
    pub m: u64,
    exp: u64,
    omega: E::Fr,
    omegainv: E::Fr,
    geninv: E::Fr,
    minv: E::Fr
}

impl<E: Engine> EvaluationDomain<E> {
    pub fn new(e: &E, needed: u64) -> Self {
        if needed > 268435456 {
            panic!("circuit depths larger than 2^28 are not supported");
        }

        let mut m = 1;
        let mut exp = 0;
        while m < needed {
            m *= 2;
            exp += 1;

            assert!(exp < E::Fr::s(e));
        }

        let mut omega = E::Fr::root_of_unity(e);
        for _ in exp..E::Fr::s(e) {
            omega.square(e);
        }

        EvaluationDomain {
            m: m,
            exp: exp,
            omega: omega,
            omegainv: omega.inverse(e).unwrap(),
            geninv: E::Fr::multiplicative_generator(e).inverse(e).unwrap(),
            minv: E::Fr::from_u64(e, m).inverse(e).unwrap()
        }
    }

    pub fn z(&self, e: &E, tau: &E::Fr) -> E::Fr {
        let mut tmp = tau.pow(e, &[self.m]);
        tmp.sub_assign(e, &E::Fr::one(e));

        tmp
    }

    pub fn ifft<T: Group<E>>(&self, e: &E, v: &mut [T])
    {
        assert!(v.len() == self.m as usize);
        self._fft(e, v, &self.omegainv);
        for v in v {
            v.group_mul_assign(e, &self.minv);
        }
    }

    fn mul_coset(&self, e: &E, v: &mut [E::Fr], g: &E::Fr)
    {
        let mut u = *g;
        for v in v.iter_mut().skip(1) {
            v.mul_assign(e, &u);
            u.mul_assign(e, g);
        }
    }

    pub fn coset_fft(&self, e: &E, v: &mut [E::Fr])
    {
        self.mul_coset(e, v, &E::Fr::multiplicative_generator(e));
        self.fft(e, v);
    }

    pub fn icoset_fft(&self, e: &E, v: &mut [E::Fr])
    {
        self.ifft(e, v);
        self.mul_coset(e, v, &self.geninv);
    }

    pub fn divide_by_z_on_coset(&self, e: &E, v: &mut [E::Fr])
    {
        let i = self.z(e, &E::Fr::multiplicative_generator(e)).inverse(e).unwrap();
        for v in v {
            v.mul_assign(e, &i);
        }
    }

    pub fn fft<T: Group<E>>(&self, e: &E, a: &mut [T])
    {
        self._fft(e, a, &self.omega);
    }

    fn _fft<T: Group<E>>(&self, e: &E, a: &mut [T], omega: &E::Fr)
    {
        fn bitreverse(mut n: usize, l: u64) -> usize {
            let mut r = 0;
            for _ in 0..l {
                r = (r << 1) | (n & 1);
                n >>= 1;
            }
            r
        }

        for k in 0..(self.m as usize) {
            let rk = bitreverse(k, self.exp);
            if k < rk {
                let tmp1 = a[rk];
                let tmp2 = a[k];
                a[rk] = tmp2;
                a[k] = tmp1;
            }
        }

        let mut m = 1;
        for _ in 0..self.exp {
            let w_m = omega.pow(e, &[(self.m / (2*m)) as u64]);

            let mut k = 0;
            while k < self.m {
                let mut w = E::Fr::one(e);
                for j in 0..m {
                    let mut t = a[(k+j+m) as usize];
                    t.group_mul_assign(e, &w);
                    let mut tmp = a[(k+j) as usize];
                    tmp.group_sub_assign(e, &t);
                    a[(k+j+m) as usize] = tmp;
                    a[(k+j) as usize].group_add_assign(e, &t);
                    w.mul_assign(e, &w_m);
                }

                k += 2*m;
            }

            m *= 2;
        }
    }
}

// Test multiplying various (low degree) polynomials together and
// comparing with naive evaluations.
#[test]
fn polynomial_arith() {
    use curves::*;
    use curves::bls381::Bls381;
    use rand;

    fn test_mul<E: Engine, R: rand::Rng>(e: &E, rng: &mut R)
    {
        for coeffs_a in 1..70 {
            for coeffs_b in 1..70 {
                let final_degree = coeffs_a + coeffs_b - 1;

                let domain = EvaluationDomain::new(e, final_degree as u64);
                let mut a: Vec<_> = (0..coeffs_a).map(|_| E::Fr::random(e, rng)).collect();
                let mut b: Vec<_> = (0..coeffs_b).map(|_| E::Fr::random(e, rng)).collect();

                // naive evaluation
                let mut naive = vec![E::Fr::zero(); domain.m as usize];
                for (i1, a) in a.iter().enumerate() {
                    for (i2, b) in b.iter().enumerate() {
                        let mut prod = *a;
                        prod.mul_assign(e, b);
                        naive[i1 + i2].add_assign(e, &prod);
                    }
                }

                a.resize(domain.m as usize, E::Fr::zero());
                b.resize(domain.m as usize, E::Fr::zero());
                let mut c = vec![];
                c.resize(domain.m as usize, E::Fr::zero());

                domain.fft(e, &mut a);
                domain.fft(e, &mut b);

                for ((a, b), c) in a.iter().zip(b.iter()).zip(c.iter_mut()) {
                    *c = *a;
                    c.mul_assign(e, b);
                }

                domain.ifft(e, &mut c);

                for (naive, fft) in naive.iter().zip(c.iter()) {
                    assert_eq!(naive, fft);
                }
            }
        }
    }

    let e = &Bls381::new();
    let rng = &mut rand::thread_rng();

    test_mul(e, rng);
}
