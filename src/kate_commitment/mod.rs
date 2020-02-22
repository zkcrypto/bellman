use crate::pairing::{Engine, CurveAffine, CurveProjective};
use crate::ff::{Field, PrimeField};
use crate::worker::Worker;
use crate::plonk::polynomials::*;
use std::sync::Arc;
use crate::multiexp;
use crate::SynthesisError;

pub trait CrsType {}

pub struct CrsForMonomialForm;
pub struct CrsForLagrangeForm;
pub struct CrsForLagrangeFormOnCoset;

impl CrsType for CrsForMonomialForm {}
impl CrsType for CrsForLagrangeForm {}
impl CrsType for CrsForLagrangeFormOnCoset {}


pub struct Crs<E: Engine, T: CrsType> {
    pub g1_bases: Arc<Vec<E::G1Affine>>,
    pub g2_monomial_bases: Arc<Vec<E::G2Affine>>,

    _marker: std::marker::PhantomData<T>
}

impl<E: Engine> Crs<E, CrsForMonomialForm> {
    pub fn dummy_crs(size: usize) -> Self {
        assert!(size.is_power_of_two());

        let g1 = vec![E::G1Affine::one(); size];
        let g2 = vec![E::G2Affine::one(); 2];

        Self {
            g1_bases: Arc::new(g1),
            g2_monomial_bases: Arc::new(g2),
        
            _marker: std::marker::PhantomData
        }
    }
}

impl<E: Engine> Crs<E, CrsForLagrangeForm> {
    pub fn dummy_crs(size: usize, _worker: &Worker) -> Self {
        assert!(size.is_power_of_two());

        // let ones = vec![E::Fr::one(); size];
        // let ones = Polynomial::<E::Fr, Values>::from_values(ones).expect("must fit into some domain");
        // let ones_coeffs = ones.ifft(&worker);

        let g1 = vec![E::G1Affine::one(); size];
        let g2 = vec![E::G2Affine::one(); 2];

        // let bases = {
        //     use crate::pairing::Wnaf;

        //     // Compute G1 window table
        //     let mut g1_wnaf = Wnaf::new();
        //     let g1 = E::G1::one();
        //     let g1_wnaf = g1_wnaf.base(g1, size);

        //     let mut bases = vec![g1; size];

        //     // Compute the H query with multiple threads
        //     worker.scope(bases.len(), |scope, chunk| {
        //         for (h, p) in bases.chunks_mut(chunk).zip(powers_of_tau.chunks(chunk))
        //         {
        //             let mut g1_wnaf = g1_wnaf.shared();
        //             scope.spawn(move |_| {
        //                 // Set values of the H query to g1^{(tau^i * t(tau)) / delta}
        //                 for (h, p) in h.iter_mut().zip(p.iter())
        //                 {
        //                     // Exponentiate
        //                     *h = g1_wnaf.scalar(p.into_repr());
        //                 }

        //                 // Batch normalize
        //                 <<Eng as Engine>::G1 as CurveProjective>::batch_normalization(h);
        //             });
        //         }
        //     });

        //     bases.iter().map(|el| el.into_affine()).collect::<Vec<_>>()
        // };

        Self {
            g1_bases: Arc::new(g1),
            g2_monomial_bases: Arc::new(g2),
        
            _marker: std::marker::PhantomData
        }
    }
}

impl<E: Engine> Crs<E, CrsForLagrangeFormOnCoset> {
    pub fn dummy_crs(size: usize, _worker: &Worker) -> Self {
        assert!(size.is_power_of_two());

        let g1 = vec![E::G1Affine::one(); size];
        let g2 = vec![E::G2Affine::one(); 2];

        Self {
            g1_bases: Arc::new(g1),
            g2_monomial_bases: Arc::new(g2),
        
            _marker: std::marker::PhantomData
        }
    }
}

pub(crate) fn elements_into_representations<E: Engine>(
    worker: &Worker,
    scalars: &[E::Fr]
) -> Result<Vec<<E::Fr as PrimeField>::Repr>, SynthesisError>
{   
    let mut representations = vec![<E::Fr as PrimeField>::Repr::default(); scalars.len()];
    worker.scope(scalars.len(), |scope, chunk| {
        for (scalar, repr) in scalars.chunks(chunk)
                    .zip(representations.chunks_mut(chunk)) {
            scope.spawn(move |_| {
                for (scalar, repr) in scalar.iter()
                                        .zip(repr.iter_mut()) {
                    *repr = scalar.into_repr();
                }
            });
        }
    });

    Ok(representations)
}

pub fn commit_using_monomials<E: Engine>(
    poly: &Polynomial<E::Fr, Coefficients>,
    crs: &Crs<E, CrsForMonomialForm>,
    worker: &Worker
) -> Result<<E::G1Affine as CurveAffine>::Projective, SynthesisError> {
    let scalars_repr = elements_into_representations::<E>(
        &worker,
        &poly.as_ref()
    )?;

    multiexp::dense_multiexp::<E::G1Affine>(
        &worker,
        &crs.g1_bases[..scalars_repr.len()],
        &scalars_repr
    )
}

pub fn commit_using_values<E: Engine>(
    poly: &Polynomial<E::Fr, Values>,
    crs: &Crs<E, CrsForLagrangeForm>,
    worker: &Worker
) -> Result<<E::G1Affine as CurveAffine>::Projective, SynthesisError> {
    assert_eq!(poly.size(), crs.g1_bases.len());
    let scalars_repr = elements_into_representations::<E>(
        &worker,
        &poly.as_ref()
    )?;

    multiexp::dense_multiexp::<E::G1Affine>(
        &worker,
        &crs.g1_bases,
        &scalars_repr
    )
}

pub fn commit_using_values_on_coset<E: Engine>(
    poly: &Polynomial<E::Fr, Values>,
    crs: &Crs<E, CrsForLagrangeFormOnCoset>,
    worker: &Worker
) -> Result<<E::G1Affine as CurveAffine>::Projective, SynthesisError> {
    assert_eq!(poly.size(), crs.g1_bases.len());
    let scalars_repr = elements_into_representations::<E>(
        &worker,
        &poly.as_ref()
    )?;

    multiexp::dense_multiexp::<E::G1Affine>(
        &worker,
        &crs.g1_bases,
        &scalars_repr
    )
}


