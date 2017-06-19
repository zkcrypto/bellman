use super::{Engine, Field, SnarkField, PrimeField, Group};
use crossbeam;
use num_cpus;

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
        best_fft(e, v, &self.omegainv, self.exp);

        let chunk = (v.len() / num_cpus::get()) + 1;

        crossbeam::scope(|scope| {
            for v in v.chunks_mut(chunk) {
                scope.spawn(move || {
                    for v in v {
                        v.group_mul_assign(e, &self.minv);
                    }
                });
            }
        });
    }

    fn mul_coset(&self, e: &E, v: &mut [E::Fr], g: &E::Fr)
    {
        let chunk = (v.len() / num_cpus::get()) + 1;

        crossbeam::scope(|scope| {
            for (i, v) in v.chunks_mut(chunk).enumerate() {
                scope.spawn(move || {
                    let mut u = g.pow(e, &[(i * chunk) as u64]);
                    for v in v.iter_mut() {
                        v.mul_assign(e, &u);
                        u.mul_assign(e, g);
                    }
                });
            }
        });
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

        let chunk = (v.len() / num_cpus::get()) + 1;

        crossbeam::scope(|scope| {
            for v in v.chunks_mut(chunk) {
                scope.spawn(move || {
                    for v in v {
                        v.mul_assign(e, &i);
                    }
                });
            }
        });
    }

    pub fn mul_assign(&self, e: &E, a: &mut [E::Fr], b: Vec<E::Fr>) {
        assert_eq!(a.len(), b.len());

        let chunk = (a.len() / num_cpus::get()) + 1;

        crossbeam::scope(|scope| {
            for (a, b) in a.chunks_mut(chunk).zip(b.chunks(chunk)) {
                scope.spawn(move || {
                    for (a, b) in a.iter_mut().zip(b.iter()) {
                        a.mul_assign(e, b);
                    }
                });
            }
        });
    }

    pub fn sub_assign(&self, e: &E, a: &mut [E::Fr], b: Vec<E::Fr>) {
        assert_eq!(a.len(), b.len());

        let chunk = (a.len() / num_cpus::get()) + 1;

        crossbeam::scope(|scope| {
            for (a, b) in a.chunks_mut(chunk).zip(b.chunks(chunk)) {
                scope.spawn(move || {
                    for (a, b) in a.iter_mut().zip(b.iter()) {
                        a.sub_assign(e, b);
                    }
                });
            }
        });
    }

    pub fn fft<T: Group<E>>(&self, e: &E, a: &mut [T])
    {
        best_fft(e, a, &self.omega, self.exp);
    }
}

fn best_fft<E: Engine, T: Group<E>>(e: &E, a: &mut [T], omega: &E::Fr, log_n: u64)
{
    let log_cpus = get_log_cpus();

    if log_n < log_cpus {
        serial_fft(e, a, omega, log_n);
    } else {
        parallel_fft(e, a, omega, log_n, log_cpus);
    }
}

fn parallel_fft<E: Engine, T: Group<E>>(e: &E, a: &mut [T], omega: &E::Fr, log_n: u64, log_cpus: u64)
{
    assert!(log_n >= log_cpus);

    let num_cpus = 1 << log_cpus;
    let log_new_n = log_n - log_cpus;
    let mut tmp = vec![vec![T::group_zero(e); 1 << log_new_n]; num_cpus];
    let omega_num_cpus = omega.pow(e, &[num_cpus as u64]);

    crossbeam::scope(|scope| {
        let a = &*a;

        for (j, tmp) in tmp.iter_mut().enumerate() {
            scope.spawn(move || {
                let omega_j = omega.pow(e, &[j as u64]);
                let omega_step = omega.pow(e, &[(j as u64) << log_new_n]);

                let mut elt = E::Fr::one(e);
                for i in 0..(1 << log_new_n) {
                    for s in 0..num_cpus {
                        let idx = (i + (s << log_new_n)) % (1 << log_n);
                        let mut t = a[idx];
                        t.group_mul_assign(e, &elt);
                        tmp[i].group_add_assign(e, &t);
                        elt.mul_assign(e, &omega_step);
                    }
                    elt.mul_assign(e, &omega_j);
                }

                serial_fft(e, tmp, &omega_num_cpus, log_new_n);
            });
        }
    });

    let chunk = (a.len() / num_cpus) + 1;

    crossbeam::scope(|scope| {
        let tmp = &tmp;

        for (idx, a) in a.chunks_mut(chunk).enumerate() {
            scope.spawn(move || {
                let mut idx = idx * chunk;
                let mask = (1 << log_cpus) - 1;
                for a in a {
                    *a = tmp[idx & mask][idx >> log_cpus];
                    idx += 1;
                }
            });
        }
    });
}

fn serial_fft<E: Engine, T: Group<E>>(e: &E, a: &mut [T], omega: &E::Fr, log_n: u64)
{
    fn bitreverse(mut n: usize, l: u64) -> usize {
        let mut r = 0;
        for _ in 0..l {
            r = (r << 1) | (n & 1);
            n >>= 1;
        }
        r
    }

    let n = a.len();
    assert_eq!(n, 1 << log_n);

    for k in 0..n {
        let rk = bitreverse(k, log_n);
        if k < rk {
            let tmp1 = a[rk];
            let tmp2 = a[k];
            a[rk] = tmp2;
            a[k] = tmp1;
        }
    }

    let mut m = 1;
    for _ in 0..log_n {
        let w_m = omega.pow(e, &[(n / (2*m)) as u64]);

        let mut k = 0;
        while k < n {
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

fn get_log_cpus() -> u64 {
    let num = num_cpus::get();
    log2_floor(num)
}

fn log2_floor(num: usize) -> u64 {
    assert!(num > 0);

    let mut pow = 0;

    while (1 << (pow+1)) <= num {
        pow += 1;
    }

    pow
}

#[test]
fn test_log2_floor() {
    assert_eq!(log2_floor(1), 0);
    assert_eq!(log2_floor(2), 1);
    assert_eq!(log2_floor(3), 1);
    assert_eq!(log2_floor(4), 2);
    assert_eq!(log2_floor(5), 2);
    assert_eq!(log2_floor(6), 2);
    assert_eq!(log2_floor(7), 2);
    assert_eq!(log2_floor(8), 3);
}

#[test]
fn parallel_fft_consistency() {
    use curves::*;
    use curves::bls381::{Bls381, Fr};
    use std::cmp::min;
    use rand;

    let e = &Bls381::new();
    let rng = &mut rand::thread_rng();

    for log_d in 0..10 {
        let d = 1 << log_d;
        let domain = EvaluationDomain::new(e, d);
        assert_eq!(domain.m, d);

        for log_cpus in 0..min(log_d, 3) {
            let mut v1 = (0..d).map(|_| Fr::random(e, rng)).collect::<Vec<_>>();
            let mut v2 = v1.clone();

            parallel_fft(e, &mut v1, &domain.omega, log_d, log_cpus);
            serial_fft(e, &mut v2, &domain.omega, log_d);

            assert_eq!(v1, v2);
        }
    }
}
