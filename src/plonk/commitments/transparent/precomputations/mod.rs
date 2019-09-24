use crate::pairing::ff::PrimeField;

use crate::plonk::domains::Domain;
use crate::multicore::Worker;
use crate::plonk::fft::distribute_powers;
use crate::plonk::commitments::transparent::fri::FriPrecomputations;

pub struct PrecomputedOmegas<F: PrimeField> {
    pub omegas: Vec<F>,
    pub coset: Vec<F>,
    pub omegas_inv: Vec<F>,
    domain_size: usize
}

impl<F: PrimeField> PrecomputedOmegas<F> {
    pub fn new_for_domain(domain: &Domain<F>, worker: &Worker) -> Self {
        let domain_size = domain.size as usize;
        let precomputation_size = domain_size/2;

        let omega = domain.generator;
        let omega_inv = domain.generator.inverse().expect("must exist");

        let mut omegas = vec![F::zero(); domain_size];
        let mut omegas_inv = vec![F::zero(); precomputation_size];

        worker.scope(omegas.len(), |scope, chunk| {
            for (i, v) in omegas.chunks_mut(chunk).enumerate() {
                scope.spawn(move |_| {
                    let mut u = omega.pow(&[(i * chunk) as u64]);
                    for v in v.iter_mut() {
                        *v = u;
                        u.mul_assign(&omega);
                    }
                });
            }
        });

        worker.scope(omegas_inv.len(), |scope, chunk| {
            for (i, v) in omegas_inv.chunks_mut(chunk).enumerate() {
                scope.spawn(move |_| {
                    let mut u = omega_inv.pow(&[(i * chunk) as u64]);
                    for v in v.iter_mut() {
                        *v = u;
                        u.mul_assign(&omega_inv);
                    }
                });
            }
        });

        let mut coset = omegas.clone();
        let mult_generator = F::multiplicative_generator();

        worker.scope(coset.len(), |scope, chunk| {
            for v in coset.chunks_mut(chunk) {
                scope.spawn(move |_| {
                    for v in v.iter_mut() {
                        v.mul_assign(&mult_generator);
                    }
                });
            }
        });

        PrecomputedOmegas{
            omegas,
            coset,
            omegas_inv,
            domain_size
        }
    }
}

impl<F: PrimeField> FriPrecomputations<F> for PrecomputedOmegas<F>{
    fn omegas_inv_ref(&self) -> &[F] {
        &self.omegas_inv[..]
    }

    fn domain_size(&self) -> usize {
        self.domain_size
    }
}

pub struct PrecomputedInvOmegas<F: PrimeField> {
    pub omegas_inv: Vec<F>,
    domain_size: usize
}

impl<F: PrimeField> PrecomputedInvOmegas<F> {
    pub fn new_for_domain(domain: &Domain<F>, worker: &Worker) -> Self {
        let domain_size = domain.size as usize;
        let precomputation_size = domain_size/2;

        let omega = domain.generator;
        let omega_inv = domain.generator.inverse().expect("must exist");

        let mut omegas_inv = vec![F::zero(); precomputation_size];

        worker.scope(omegas_inv.len(), |scope, chunk| {
            for (i, v) in omegas_inv.chunks_mut(chunk).enumerate() {
                scope.spawn(move |_| {
                    let mut u = omega_inv.pow(&[(i * chunk) as u64]);
                    for v in v.iter_mut() {
                        *v = u;
                        u.mul_assign(&omega_inv);
                    }
                });
            }
        });

        PrecomputedInvOmegas{
            omegas_inv,
            domain_size
        }
    }
}

impl<F: PrimeField> FriPrecomputations<F> for PrecomputedInvOmegas<F>{
    fn omegas_inv_ref(&self) -> &[F] {
        &self.omegas_inv[..]
    }

    fn domain_size(&self) -> usize {
        self.domain_size
    }
}