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

    pub fn crs_42(size: usize, worker: &Worker) -> Self {
        // kind of how ceremony would work
        assert!(size.is_power_of_two());

        let mut g2 = vec![E::G2Affine::one(); 2];

        use crate::group::Scalar;
        use crate::domain::EvaluationDomain;
        use crate::pairing::Wnaf;

        let mut coeffs = vec![Scalar::<E>(E::Fr::one()); size];
        
        {
            let gen = E::Fr::from_str("42").unwrap();

            g2[1] = g2[1].mul(gen.into_repr()).into_affine();

            worker.scope(coeffs.len(), |scope, chunk| {
                for (i, p) in coeffs.chunks_mut(chunk).enumerate()
                {
                    scope.spawn(move |_| {
                        let mut current_p = gen.pow(&[(i*chunk) as u64]);

                        for p in p.iter_mut() {
                            p.0 = current_p;
                            current_p.mul_assign(&gen);
                        }
                    });
                }
            });
        }

        let mut g1_wnaf = Wnaf::new();
        let g1_wnaf = g1_wnaf.base(E::G1Affine::one().into_projective(), size);

        let mut g1 = vec![E::G1Affine::zero().into_projective(); size];

        worker.scope(g1.len(), |scope, chunk| {
            for (g1, p) in g1.chunks_mut(chunk).zip(coeffs.chunks(chunk))
            {
                let mut g1_wnaf = g1_wnaf.shared();
                scope.spawn(move |_| {
                    for (g1, p) in g1.iter_mut().zip(p.iter())
                    {
                        // Compute final exponent
                        let exp = p.0;

                        // Exponentiate
                        *g1 = g1_wnaf.scalar(exp.into_repr());
                    }

                    // Batch normalize
                    E::G1::batch_normalization(g1);
                });
            }
        });

        let g1: Vec<_> = g1.into_iter().map(|el| el.into_affine()).collect();

        Self {
            g1_bases: Arc::new(g1),
            g2_monomial_bases: Arc::new(g2),
        
            _marker: std::marker::PhantomData
        }
    }
}

impl<E: Engine> Crs<E, CrsForLagrangeForm> {
    pub fn crs_42(size: usize, worker: &Worker) -> Self {
        let tmp = Crs::<E, CrsForMonomialForm>::crs_42(size, &worker);

        Self::from_powers(&tmp, size, &worker)
    }

    pub fn from_powers(powers: &Crs::<E, CrsForMonomialForm>, size: usize, worker: &Worker) -> Self {
        assert!(size.is_power_of_two());
        assert!(size <= powers.g1_bases.len());

        let g2 = powers.g2_monomial_bases.as_ref().to_vec();
        let g1 = powers.g1_bases.as_ref()[..size].to_vec();

        let g1 = g1.into_iter().map(|el| Point(el.into_projective())).collect();

        use crate::group::Point;
        use crate::domain::EvaluationDomain;

        let mut g1 = EvaluationDomain::from_coeffs(g1).expect("must fit into the domain");
        g1.transform_powers_of_tau_into_lagrange_basis(&worker);
        let mut g1: Vec<_> = g1.into_coeffs().into_iter().map(|el| el.0).collect();

        worker.scope(g1.len(), |scope, chunk| {
            for g1 in g1.chunks_mut(chunk)
            {
                scope.spawn(move |_| {
                    // Batch normalize
                    E::G1::batch_normalization(g1);
                });
            }
        });

        let g1: Vec<_> = g1.into_iter().map(|el| el.into_affine()).collect();

        Self {
            g1_bases: Arc::new(g1),
            g2_monomial_bases: Arc::new(g2),
        
            _marker: std::marker::PhantomData
        }
    }
}

impl<E: Engine> Crs<E, CrsForLagrangeFormOnCoset> {
    pub fn crs_42(size: usize, worker: &Worker) -> Self {
        let tmp = Crs::<E, CrsForMonomialForm>::crs_42(size, &worker);

        Self::from_powers(&tmp, size, &worker)
    }

    pub fn from_powers(powers: &Crs::<E, CrsForMonomialForm>, size: usize, worker: &Worker) -> Self {
        assert!(size.is_power_of_two());
        assert!(size <= powers.g1_bases.len());

        let g2 = powers.g2_monomial_bases.as_ref().to_vec();
        let g1 = powers.g1_bases.as_ref()[..size].to_vec();

        let g1: Vec<_> = g1.into_iter().map(|el| Point(el.into_projective())).collect();

        use crate::group::Point;
        use crate::domain::EvaluationDomain;

        let mut g1 = EvaluationDomain::from_coeffs(g1).expect("must fit into the domain");

        g1.transform_powers_of_tau_into_lagrange_basis_on_coset(&worker);
        let mut g1: Vec<_> = g1.into_coeffs().into_iter().map(|el| el.0).collect();

        worker.scope(g1.len(), |scope, chunk| {
            for g1 in g1.chunks_mut(chunk)
            {
                scope.spawn(move |_| {
                    // Batch normalize
                    E::G1::batch_normalization(g1);
                });
            }
        });

        let g1: Vec<_> = g1.into_iter().map(|el| el.into_affine()).collect();

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
) -> Result<E::G1Affine, SynthesisError> {
    println!("Committing coefficients");
    let scalars_repr = elements_into_representations::<E>(
        &worker,
        &poly.as_ref()
    )?;

    let res = multiexp::dense_multiexp::<E::G1Affine>(
        &worker,
        &crs.g1_bases[..scalars_repr.len()],
        &scalars_repr
    )?;

    Ok(res.into_affine())
}

pub fn commit_using_values<E: Engine>(
    poly: &Polynomial<E::Fr, Values>,
    crs: &Crs<E, CrsForLagrangeForm>,
    worker: &Worker
) -> Result<E::G1Affine, SynthesisError> {
    println!("Committing values over domain");
    assert_eq!(poly.size(), crs.g1_bases.len());
    let scalars_repr = elements_into_representations::<E>(
        &worker,
        &poly.as_ref()
    )?;

    let res = multiexp::dense_multiexp::<E::G1Affine>(
        &worker,
        &crs.g1_bases,
        &scalars_repr
    )?;

    Ok(res.into_affine())
}

pub fn commit_using_values_on_coset<E: Engine>(
    poly: &Polynomial<E::Fr, Values>,
    crs: &Crs<E, CrsForLagrangeFormOnCoset>,
    worker: &Worker
) -> Result<E::G1Affine , SynthesisError> {
    println!("Committing values over coset");
    assert_eq!(poly.size(), crs.g1_bases.len());
    let scalars_repr = elements_into_representations::<E>(
        &worker,
        &poly.as_ref()
    )?;

    let res = multiexp::dense_multiexp::<E::G1Affine>(
        &worker,
        &crs.g1_bases,
        &scalars_repr
    )?;

    Ok(res.into_affine())
}

pub fn open_from_monomials<E: Engine>(
    poly: &Polynomial<E::Fr, Coefficients>,
    at: E::Fr,
    _expected_value: E::Fr,
    crs: &Crs<E, CrsForMonomialForm>,
    worker: &Worker
) -> Result<E::G1Affine, SynthesisError> {
    assert!(poly.size().is_power_of_two());
    let division_result = divide_single::<E>(poly.as_ref(), at);
    assert!(division_result.len().is_power_of_two());
    let division_result = Polynomial::from_coeffs(division_result)?;

    let opening_proof = commit_using_monomials(
        &division_result, 
        &crs, 
        &worker
    )?;

    Ok(opening_proof)
}

pub fn open_from_values<E: Engine>(
    poly: &Polynomial<E::Fr, Values>,
    at: E::Fr,
    expected_value: E::Fr,
    crs: &Crs<E, CrsForLagrangeForm>,
    worker: &Worker
) -> Result<E::G1Affine, SynthesisError> {
    assert!(poly.size().is_power_of_two());
    let division_result = vec![E::Fr::one(); poly.size()];
    let mut division_result = Polynomial::from_values(division_result)?;
    division_result.distribute_powers(&worker, division_result.omega);
    division_result.sub_constant(&worker, &at);
    division_result.batch_inversion(&worker)?;

    worker.scope(division_result.size(), |scope, chunk_size| {
        for (result, values) in division_result.as_mut().chunks_mut(chunk_size)
                                            .zip(poly.as_ref().chunks(chunk_size))
        {
            scope.spawn(move |_| {
                for (r, &val) in result.iter_mut().zip(values.iter()) {
                    let mut tmp = val;
                    tmp.sub_assign(&expected_value);
                    r.mul_assign(&tmp);
                }
            });
        }
    });

    let opening_proof = commit_using_values(&division_result, &crs, &worker)?;

    Ok(opening_proof)
}

pub fn open_from_values_on_coset<E: Engine>(
    poly: &Polynomial<E::Fr, Values>,
    coset_factor: E::Fr,
    at: E::Fr,
    expected_value: E::Fr,
    crs: &Crs<E, CrsForLagrangeFormOnCoset>,
    worker: &Worker
) -> Result<E::G1Affine, SynthesisError> {
    assert!(poly.size().is_power_of_two());
    let division_result = vec![coset_factor; poly.size()];
    let mut division_result = Polynomial::from_values(division_result)?; // [g, g, g, g, ...]
    division_result.distribute_powers(&worker, division_result.omega); // [g, g*omega, g*omega^2, ...]
    division_result.sub_constant(&worker, &at); // g - z, g*omega - z, g*omega^2 - z, ...]
    division_result.batch_inversion(&worker)?;

    worker.scope(division_result.size(), |scope, chunk_size| {
        for (result, values) in division_result.as_mut().chunks_mut(chunk_size)
                                            .zip(poly.as_ref().chunks(chunk_size))
        {
            scope.spawn(move |_| {
                for (r, &val) in result.iter_mut().zip(values.iter()) {
                    let mut tmp = val;
                    tmp.sub_assign(&expected_value);
                    r.mul_assign(&tmp);
                }
            });
        }
    });

    let opening_proof = commit_using_values_on_coset(&division_result, &crs, &worker)?;

    Ok(opening_proof)
}

pub fn is_valid_opening<E: Engine>(
    commitment: E::G1Affine,
    z: E::Fr,
    opening_value: E::Fr,
    opening_proof: E::G1Affine,
    g2_by_x: E::G2Affine
) -> bool {
    // (f(x) - f(z))/(x - z) = op(x)

    // f(x) = f(z) + op(x) * (x - z)
    // e(f(x) - f(z) + z*op(x), 1) = e(op(x), x)
    // e(f(x) - f(z) + z*op(x), 1) * e(-op(x), x) == 1 // e(0, 0)

    let mut pair_with_1_part = commitment.into_projective();
    let gen_by_opening_value = E::G1Affine::one().mul(opening_value.into_repr());
    let proof_by_z = opening_proof.mul(z.into_repr());

    pair_with_1_part.sub_assign(&gen_by_opening_value);
    pair_with_1_part.add_assign(&proof_by_z);

    let mut pair_with_x_part = opening_proof;
    pair_with_x_part.negate();

    let result = E::final_exponentiation(
        &E::miller_loop(
            &[
                (&pair_with_1_part.into_affine().prepare(), &E::G2Affine::one().prepare()),
                (&pair_with_x_part.prepare(), &g2_by_x.prepare()),
            ]
    ));
    
    if let Some(res) = result {
        return res == E::Fqk::one();
    }
    
    false
}

fn divide_single<E: Engine>(
    poly: &[E::Fr],
    opening_point: E::Fr,
) -> Vec<E::Fr> {
    // we are only interested in quotient without a reminder, so we actually don't need opening value
    let mut b = opening_point;
    b.negate();

    let mut q = vec![E::Fr::zero(); poly.len()];

    let mut tmp = E::Fr::zero();
    let mut found_one = false;
    for (q, r) in q.iter_mut().rev().skip(1).zip(poly.iter().rev()) {
        if !found_one {
            if r.is_zero() {
                continue
            } else {
                found_one = true;
            }
        }

        let mut lead_coeff = *r;
        lead_coeff.sub_assign(&tmp);
        *q = lead_coeff;
        tmp = lead_coeff;
        tmp.mul_assign(&b);
    }

    q
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::pairing::bn256::{Bn256, Fr};
    use crate::worker::Worker;
    use crate::ff::{PrimeField, Field};
    use crate::plonk::polynomials::*;

    #[test]
    fn test_transformations_of_crs_1() {
        let worker = Worker::new();

        let monomial = Crs::<Bn256, CrsForMonomialForm>::crs_42(1, &worker);
        let lagrange = Crs::<Bn256, CrsForLagrangeForm>::crs_42(1, &worker);
        let lagrange_coset = Crs::<Bn256, CrsForLagrangeFormOnCoset>::crs_42(1, &worker);

        println!("Monomial = {:?}", monomial.g1_bases);
        println!("Lagrange = {:?}", lagrange.g1_bases);
        println!("Lagrange coset = {:?}", lagrange_coset.g1_bases);
    }

    #[test]
    fn test_transformations_of_crs_2() {
        let worker = Worker::new();

        let monomial = Crs::<Bn256, CrsForMonomialForm>::crs_42(2, &worker);
        let lagrange = Crs::<Bn256, CrsForLagrangeForm>::crs_42(2, &worker);
        let lagrange_coset = Crs::<Bn256, CrsForLagrangeFormOnCoset>::crs_42(2, &worker);

        println!("Monomial = {:?}", monomial.g1_bases);
        println!("Lagrange = {:?}", lagrange.g1_bases);
        println!("Lagrange coset = {:?}", lagrange_coset.g1_bases);

        // for a poly in a form a + bx
        // commitment is a + b*tau
        // values on domain are a+b, a-b
        // commitment bases are (1+tau)/2, (1-tau)/2
        // commitment is (a+b)(1+tau)/2 + (a-b)(1-tau)/2 = a/2 + a*tau/2 + b/2 + b*tau/2 + a/2 - a*tau/2 - b/2 + b*tau/2 = a + tau*b
        // valus on coset are a + gen*b, a - gen*b
        // commitment is a*(b_0 + b_1) + gen*b*(b_0 - b_1) = a * tau*b
        // so bases must be b_0 + b_1 = 1 and b_0 - b_1 = tau / gen
        // so b_0 = 1 + tau/gen/2, b_1 = 1 - tau/gen/2


        let one = Fr::one();

        let mut two = Fr::one();
        two.double();

        let poly = Polynomial::<Fr, Coefficients>::from_coeffs(vec![one, two]).unwrap();
        let values = poly.clone().fft(&worker);
        let values_on_coset = poly.clone().coset_fft(&worker);

        let mut tmp = Fr::multiplicative_generator();
        tmp.mul_assign(&two);
        tmp.add_assign(&one);

        assert!(tmp == values_on_coset.as_ref()[0]);

        let commitment = commit_using_monomials(&poly, &monomial, &worker).unwrap();
        let commitment_values = commit_using_values(&values, &lagrange, &worker).unwrap();
        let commitment_values_on_coset = commit_using_values_on_coset(&values_on_coset, &lagrange_coset, &worker).unwrap();

        assert!(commitment == commitment_values);
        assert!(commitment == commitment_values_on_coset);

    }

    #[test]
    fn test_transformations_of_crs_4() {
        let worker = Worker::new();

        let monomial = Crs::<Bn256, CrsForMonomialForm>::crs_42(4, &worker);
        let lagrange = Crs::<Bn256, CrsForLagrangeForm>::crs_42(4, &worker);
        let lagrange_coset = Crs::<Bn256, CrsForLagrangeFormOnCoset>::crs_42(4, &worker);

        let one = Fr::one();

        let mut two = Fr::one();
        two.double();

        let poly = Polynomial::<Fr, Coefficients>::from_coeffs(vec![one, two, one, two]).unwrap();
        let values = poly.clone().fft(&worker);
        let values_on_coset = poly.clone().coset_fft(&worker);

        let commitment = commit_using_monomials(&poly, &monomial, &worker).unwrap();
        let commitment_values = commit_using_values(&values, &lagrange, &worker).unwrap();
        let commitment_values_on_coset = commit_using_values_on_coset(&values_on_coset, &lagrange_coset, &worker).unwrap();

        assert!(commitment == commitment_values);
        assert!(commitment == commitment_values_on_coset);

    }

    #[test]
    fn test_transformations_of_crs_large() {
        let worker = Worker::new();

        let size = 1024;

        let monomial = Crs::<Bn256, CrsForMonomialForm>::crs_42(size, &worker);
        let lagrange = Crs::<Bn256, CrsForLagrangeForm>::crs_42(size, &worker);
        let lagrange_coset = Crs::<Bn256, CrsForLagrangeFormOnCoset>::crs_42(size, &worker);

        let mut two = Fr::one();
        two.double();

        let poly = Polynomial::<Fr, Coefficients>::from_coeffs(vec![two; size]).unwrap();
        let values = poly.clone().fft(&worker);
        let values_on_coset = poly.clone().coset_fft(&worker);

        let commitment = commit_using_monomials(&poly, &monomial, &worker).unwrap();
        let commitment_values = commit_using_values(&values, &lagrange, &worker).unwrap();
        let commitment_values_on_coset = commit_using_values_on_coset(&values_on_coset, &lagrange_coset, &worker).unwrap();

        assert!(commitment == commitment_values);
        assert!(commitment == commitment_values_on_coset);

    }

    #[test]
    fn test_opening_large() {
        let worker = Worker::new();

        let size = 1024;

        let monomial = Crs::<Bn256, CrsForMonomialForm>::crs_42(size, &worker);
        let lagrange = Crs::<Bn256, CrsForLagrangeForm>::crs_42(size, &worker);
        let lagrange_coset = Crs::<Bn256, CrsForLagrangeFormOnCoset>::crs_42(size, &worker);

        let mut two = Fr::one();
        two.double();

        let poly = Polynomial::<Fr, Coefficients>::from_coeffs(vec![two; size]).unwrap();
        let values = poly.clone().fft(&worker);
        let values_on_coset = poly.clone().coset_fft(&worker);

        let z = Fr::from_str("1337").unwrap();

        let poly_at_z = poly.evaluate_at(&worker, z);
        let values_at_z = values.barycentric_evaluate_at(&worker, z).unwrap();
        let valus_on_coset_at_z = values_on_coset.barycentric_over_coset_evaluate_at(&worker, z, &Fr::multiplicative_generator()).unwrap();

        assert!(poly_at_z == values_at_z);
        assert!(poly_at_z == valus_on_coset_at_z);

        let commitment = commit_using_monomials(&poly, &monomial, &worker).unwrap();
        let commitment_values = commit_using_values(&values, &lagrange, &worker).unwrap();
        let commitment_values_on_coset = commit_using_values_on_coset(&values_on_coset, &lagrange_coset, &worker).unwrap();

        assert!(commitment == commitment_values);
        assert!(commitment == commitment_values_on_coset);

        let opening_poly = open_from_monomials(&poly, z, poly_at_z, &monomial, &worker).unwrap();
        let opening_values = open_from_values(&values, z, poly_at_z, &lagrange, &worker).unwrap();
        let opening_values_on_coset = open_from_values_on_coset(&values_on_coset, Fr::multiplicative_generator(), z, poly_at_z, &lagrange_coset, &worker).unwrap();

        assert!(opening_poly == opening_values);
        assert!(opening_poly == opening_values_on_coset);

        let valid = is_valid_opening::<Bn256>(commitment, z, poly_at_z, opening_poly, monomial.g2_monomial_bases[1]);

        assert!(valid);
    }
}
