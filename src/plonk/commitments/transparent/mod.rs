use crate::pairing::ff::PrimeField;

use crate::plonk::polynomials::*;
use crate::multicore::Worker;
use super::CommitmentScheme;

pub mod precomputations;
pub mod iop;
pub mod fri;

pub mod utils;

use self::precomputations::PrecomputedInvOmegas;
use crate::plonk::domains::*;
use crate::plonk::commitments::transcript::Prng;
use crate::plonk::commitments::transparent::fri::*;
use crate::plonk::commitments::transparent::iop::*;
use crate::plonk::commitments::transcript::*;
use crate::plonk::fft::cooley_tukey_ntt::{CTPrecomputations, BitReversedOmegas};

// Such committer uses external transcript for all the operations
pub struct StatelessTransparentCommitter<
    F: PrimeField, 
    FRI: FriIop<F>,
    T: Transcript<F, Input = < < < <FRI as FriIop<F> >::IopType as IOP<F> >::Tree as IopTree<F> >::TreeHasher as IopTreeHasher<F>>::HashOutput >
>{
    max_degree_plus_one: usize,
    lde_factor: usize,
    output_coeffs_at_degree_plus_one: usize,
    num_queries: usize,
    worker: Worker,
    precomputed_inverse_omegas: PrecomputedInvOmegas<F>,
    precomputed_bitreversed_omegas: BitReversedOmegas<F>,
    _marker_fri: std::marker::PhantomData<FRI>,
    _marker_t: std::marker::PhantomData<T>
}

impl<
    F: PrimeField, 
    FRI: FriIop<F>,
    T: Transcript<F, Input = < < < <FRI as FriIop<F> >::IopType as IOP<F> >::Tree as IopTree<F> >::TreeHasher as IopTreeHasher<F>>::HashOutput >
> std::fmt::Debug for StatelessTransparentCommitter<F, FRI, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        writeln!(f, "Stateless transparent committer")
    }
}

#[derive(Debug, Clone)]
pub struct TransparentCommitterParameters {
    pub lde_factor: usize,
    pub num_queries: usize,
    pub output_coeffs_at_degree_plus_one: usize,
}

use std::time::Instant;

impl<
    F: PrimeField, 
    FRI: FriIop<F>,
    T: Transcript<F, Input = < < < <FRI as FriIop<F> >::IopType as IOP<F> >::Tree as IopTree<F> >::TreeHasher as IopTreeHasher<F>>::HashOutput >
> CommitmentScheme<F> for StatelessTransparentCommitter<F, FRI, T> {
    type Commitment = < < < <FRI as FriIop<F> >::IopType as IOP<F> >::Tree as IopTree<F> >::TreeHasher as IopTreeHasher<F>>::HashOutput;
    type OpeningProof = (FRI::Proof, Vec<Vec< (F, < < FRI as FriIop<F> >::IopType as IOP<F> >::Query) > >);
    type IntermediateData = (Polynomial<F, Values>, < FRI as FriIop<F> >::IopType);
    type Meta = TransparentCommitterParameters;
    type Prng = T;

    const REQUIRES_PRECOMPUTATION: bool = true;
    const IS_HOMOMORPHIC: bool = false;

    fn new_for_size(max_degree_plus_one: usize, meta: Self::Meta) -> Self {
        let base_size = max_degree_plus_one.next_power_of_two();
        assert!(meta.lde_factor.is_power_of_two());
        assert!(meta.output_coeffs_at_degree_plus_one.is_power_of_two());
        let lde_domain_size = base_size*meta.lde_factor;
        let base_domain = Domain::<F>::new_for_size(base_size as u64).expect("domain of large enough size should exist");
        let lde_domain = Domain::<F>::new_for_size(lde_domain_size as u64).expect("domain of large enough size should exist");
        let worker = Worker::new();
        let omegas_inv_precomp = PrecomputedInvOmegas::<F>::new_for_domain(&lde_domain, &worker);
        let omegas_bitrev_precomp = BitReversedOmegas::<F>::new_for_domain(&base_domain, &worker);

        StatelessTransparentCommitter::<F, FRI, T> {
            max_degree_plus_one: max_degree_plus_one,
            lde_factor: meta.lde_factor,
            output_coeffs_at_degree_plus_one: meta.output_coeffs_at_degree_plus_one,
            num_queries: meta.num_queries,
            worker: worker,
            precomputed_inverse_omegas: omegas_inv_precomp,
            precomputed_bitreversed_omegas: omegas_bitrev_precomp,
            _marker_fri: std::marker::PhantomData,
            _marker_t: std::marker::PhantomData
        }
    }

    fn precompute(&self, poly: &Polynomial<F, Coefficients>) -> Option<Self::IntermediateData> {
        assert!(poly.size() == self.max_degree_plus_one);
        let original_poly_lde = poly.clone().lde_using_bitreversed_ntt(&self.worker, self.lde_factor, &self.precomputed_bitreversed_omegas).expect("must make an LDE");
        // let original_poly_lde = poly.clone().lde(&self.worker, self.lde_factor).expect("must make an LDE");
        let original_tree = < < FRI as FriIop<F> >::IopType as IOP<F> >::create(&original_poly_lde.as_ref());

        Some((original_poly_lde, original_tree))
    }

    fn commit_single(&self, poly: &Polynomial<F, Coefficients>) -> (Self::Commitment, Option<Self::IntermediateData>) {
        println!("Start commit single");
        let start = Instant::now();
        let original_poly_lde = poly.clone().lde_using_bitreversed_ntt(&self.worker, self.lde_factor, &self.precomputed_bitreversed_omegas).expect("must make an LDE");
        // let original_poly_lde = poly.clone().lde(&self.worker, self.lde_factor).expect("must make an LDE");
        let original_tree = < < FRI as FriIop<F> >::IopType as IOP<F> >::create(&original_poly_lde.as_ref());
        let commitment = original_tree.get_root();

        println!("Done in {:?} for max degree {}", start.elapsed(), poly.size());
        println!("Done commit single");

        (commitment, Some((original_poly_lde, original_tree)))
        
    }

    fn commit_multiple(&self, polynomials: Vec<&Polynomial<F, Coefficients>>, degrees: Vec<usize>, aggregation_coefficient: F) -> (Self::Commitment, Option<Vec<Self::IntermediateData>>) {
        unimplemented!()
    }

    fn open_single(
        &self, 
        poly: &Polynomial<F, Coefficients>, 
        at_point: F, 
        _opening_value: F, 
        data: &Option<&Self::IntermediateData>, 
        prng: &mut Self::Prng
    ) -> Self::OpeningProof {
        println!("Start open single");
        let start = Instant::now();

        // do not need to to the subtraction cause last coefficient is never used by division
        let division_result = {
            let division_result = kate_divison_with_same_return_size(poly.as_ref(), at_point);

            division_result
        };

        let q_poly = Polynomial::<F, Coefficients>::from_coeffs(division_result).expect("must be small enough");
        let q_poly_lde = q_poly.lde_using_bitreversed_ntt(&self.worker, self.lde_factor, &self.precomputed_bitreversed_omegas).expect("must make an LDE");
        // let q_poly_lde = q_poly.lde(&self.worker, self.lde_factor).expect("must make an LDE");

        let lde_size = q_poly_lde.size();

        let fri_proto = FRI::proof_from_lde(
            &q_poly_lde, 
            self.lde_factor, 
            self.output_coeffs_at_degree_plus_one, 
            &self.precomputed_inverse_omegas, 
            &self.worker, 
            prng
        ).expect("FRI must succeed");

        for c in fri_proto.get_final_coefficients().iter() {
            prng.commit_field_element(&c);
        }

        let mut used_queries: Vec<usize> = vec![];

        let mut domain_indexes = vec![];

        // even while this is conditional, it can be changed to unconditional given large enough field

        while domain_indexes.len() < self.num_queries {
            let domain_idx = bytes_to_challenge_index(prng.get_challenge_bytes(), lde_size);
            let coset_index_values = < < <FRI as FriIop<F> >::IopType as IOP<F> >::Combiner as CosetCombiner<F>>::get_coset_for_natural_index(domain_idx, lde_size);
            let mut can_use = true;
            for v in coset_index_values.iter() {
                if used_queries.contains(&v) {
                    can_use = false;
                    break
                }
            }
            if can_use {
                domain_indexes.push(domain_idx);
                used_queries.extend(coset_index_values);
            }
        }

        let q_poly_fri_proof = FRI::prototype_into_proof(fri_proto, &q_poly_lde, domain_indexes.clone()).expect("must generate a proper proof");

        let mut original_poly_queries = vec![];

        let precomputations = if data.is_some() {
            None
        } else {
            self.precompute(&poly)
        };

        let (original_poly_lde, original_poly_lde_oracle) = if let Some((lde, oracle)) = data.as_ref() {
            (lde, oracle)
        } else if let Some((lde, oracle)) = precomputations.as_ref() {
            (lde, oracle)
        } else {
            unreachable!("precomputations are required for transparent polynomial commitment");
        };

        for idx in domain_indexes.into_iter() {
            let original_value = < < <FRI as FriIop<F> >::IopType as IOP<F> >::Combiner as CosetCombiner<F>>::get_for_natural_index(original_poly_lde.as_ref(), idx);
            let original_poly_query = original_poly_lde_oracle.query(idx, original_poly_lde.as_ref());
            original_poly_queries.push((*original_value, original_poly_query));
        }

        println!("Done in {:?} for max degree {}", start.elapsed(), poly.size());
        println!("Done open single");

        (q_poly_fri_proof, vec![original_poly_queries])

    }

    fn open_multiple(
        &self, 
        polynomials: Vec<&Polynomial<F, Coefficients>>, 
        degrees: Vec<usize>, 
        aggregation_coefficient: F, 
        at_points: Vec<F>, 
        opening_values: Vec<F>,
        data: &Option<Vec<&Self::IntermediateData>>, 
        prng: &mut Self::Prng
    ) -> Self::OpeningProof {
        println!("Start open multiple");
        let start = Instant::now();
        assert!(at_points.len() == opening_values.len());
        assert!(at_points.len() == polynomials.len());

        let max_degree = *degrees.iter().max().expect("MAX element exists");
        let min_degree = *degrees.iter().min().expect("MIN element exists");

        assert!(f64::from(max_degree as u32) / f64::from(min_degree as u32) < 2.0, "polynomials should not have too large degree difference");

        let mut division_results = vec![vec![]; polynomials.len()];

        self.worker.scope(polynomials.len(), |scope, chunk| {
            for ((p, q), at) in polynomials.chunks(chunk)
                        .zip(division_results.chunks_mut(chunk)) 
                        .zip(at_points.chunks(chunk))
                        {
                scope.spawn(move |_| {
                    for ((p, q), at) in p.iter().zip(q.iter_mut()).zip(at.iter()) {
                        let division_result = kate_divison_with_same_return_size(p.as_ref(), *at);

                        *q = division_result;
                    }
                });
            }
        });

        // aggregate starting usign the first coefficient of 1

        let mut q_poly: Option<Polynomial::<F, Coefficients>> = None;

        let mut alpha = F::one();

        for q in division_results.into_iter() {
            if let Some(q_poly) = q_poly.as_mut() {
                let q = Polynomial::<F, Coefficients>::from_coeffs(q).expect("must be small enough");
                q_poly.add_assign_scaled(&self.worker, &q, &alpha);
            } else {
                let q = Polynomial::<F, Coefficients>::from_coeffs(q).expect("must be small enough");
                q_poly = Some(q);
            }
            alpha.mul_assign(&aggregation_coefficient);
        }

        let q_poly = q_poly.expect("now it's aggregated");

        let q_poly_lde = q_poly.lde_using_bitreversed_ntt(&self.worker, self.lde_factor, &self.precomputed_bitreversed_omegas).expect("must make an LDE");

        // let q_poly_lde = q_poly.lde(&self.worker, self.lde_factor).expect("must make an LDE");

        let lde_size = q_poly_lde.size();

        let fri_proto = FRI::proof_from_lde(
            &q_poly_lde, 
            self.lde_factor, 
            self.output_coeffs_at_degree_plus_one, 
            &self.precomputed_inverse_omegas, 
            &self.worker, 
            prng
        ).expect("FRI must succeed");

        for c in fri_proto.get_final_coefficients().iter() {
            prng.commit_field_element(&c);
        }

        let mut used_queries: Vec<usize> = vec![];

        let mut domain_indexes = vec![];

        // even while this is conditional, it can be changed to unconditional given large enough field

        while domain_indexes.len() < self.num_queries {
            let domain_idx = bytes_to_challenge_index(prng.get_challenge_bytes(), lde_size);
            let coset_index_values = < < <FRI as FriIop<F> >::IopType as IOP<F> >::Combiner as CosetCombiner<F>>::get_coset_for_natural_index(domain_idx, lde_size);
            let mut can_use = true;
            for v in coset_index_values.iter() {
                if used_queries.contains(&v) {
                    can_use = false;
                    break
                }
            }
            if can_use {
                domain_indexes.push(domain_idx);
                used_queries.extend(coset_index_values);
            }
        }

        let q_poly_fri_proof = FRI::prototype_into_proof(fri_proto, &q_poly_lde, domain_indexes.clone()).expect("must generate a proper proof");

        let precomputations = if data.is_some() {
            None
        } else {
            let mut result = Vec::with_capacity(polynomials.len());
            for poly in polynomials.iter() {
                let p = self.precompute(&poly).expect("aux data is computed");
                result.push(p);
            }

            Some(result)
        };

        let mut prec_may_be = None;
        
        let data = if data.is_some() {
            data.as_ref()
        } else {
            prec_may_be = Some(precomputations.as_ref().expect("is some").iter().map(|el| el).collect::<Vec<_>>());
            prec_may_be.as_ref()
        }.expect("there is aux data in full");

        let mut queries = vec![];

        for (original_poly_lde, original_poly_lde_oracle) in data.iter() {
            let mut original_poly_queries = vec![];
            for idx in domain_indexes.clone().into_iter() {
                let original_value = < < <FRI as FriIop<F> >::IopType as IOP<F> >::Combiner as CosetCombiner<F>>::get_for_natural_index(original_poly_lde.as_ref(), idx);
                let original_poly_query = original_poly_lde_oracle.query(idx, original_poly_lde.as_ref());
                original_poly_queries.push((*original_value, original_poly_query));
            }
            queries.push(original_poly_queries);
        }

        // let mut opened_values = vec![];

        // for idx in domain_indexes.clone().into_iter() {
        //     let value = < < <FRI as FriIop<F> >::IopType as IOP<F> >::Combiner as CosetCombiner<F>>::get_for_natural_index(q_poly_lde.as_ref(), idx);
        //     opened_values.push(value);
        // }

        // println!("Will open poly at indexes {:?} for values {:?}", domain_indexes, opened_values);


        println!("Done in {:?} for max degree {}", start.elapsed(), max_degree);
        println!("Done open multiple");

        (q_poly_fri_proof, queries)
    }

    fn verify_single(&self, commitment: &Self::Commitment, at_point: F, claimed_value: F, proof: &Self::OpeningProof, prng: &mut Self::Prng) -> bool {
        let (q_poly_fri_proof, original_poly_queries_vec) = proof;

        assert!(original_poly_queries_vec.len() == 1);

        let original_poly_queries = &original_poly_queries_vec[0];

        let lde_size = self.max_degree_plus_one.next_power_of_two() * self.lde_factor;
        let lde_domain = Domain::<F>::new_for_size(lde_size as u64).expect("large enough domain must exist");

        // first get FRI challenges

        let fri_challenges = FRI::get_fri_challenges(q_poly_fri_proof, prng);

        for c in q_poly_fri_proof.get_final_coefficients().iter() {
            prng.commit_field_element(&c);
        }

        // then make expected query locations

        let mut used_queries: Vec<usize> = vec![];

        let mut domain_indexes = vec![];

        // even while this is conditional, it can be changed to unconditional given large enough field

        while domain_indexes.len() < self.num_queries {
            let domain_idx = bytes_to_challenge_index(prng.get_challenge_bytes(), lde_size);
            let coset_index_values = < < <FRI as FriIop<F> >::IopType as IOP<F> >::Combiner as CosetCombiner<F>>::get_coset_for_natural_index(domain_idx, lde_size);
            let mut can_use = true;
            for v in coset_index_values.iter() {
                if used_queries.contains(&v) {
                    can_use = false;
                    break
                }
            }
            if can_use {
                domain_indexes.push(domain_idx);
                used_queries.extend(coset_index_values);
            }
        }

        // now simulate expected values

        let mut simulated_q_poly_values = vec![];

        for (domain_idx, original_poly_query) in domain_indexes.clone().into_iter()
                                                .zip(original_poly_queries.iter()) {
            let x = lde_domain.generator.pow(&[domain_idx as u64]);

            assert!(original_poly_query.1.value() == original_poly_query.0);
        
            let mut num = original_poly_query.0;
            num.sub_assign(&claimed_value);

            let mut den = x;
            den.sub_assign(&at_point);

            let den_inversed = den.inverse().expect("denominator is unlikely to be zero in large enough field");

            let mut value_at_x = num;
            value_at_x.mul_assign(&den_inversed);

            let is_in_commitment = < <FRI as FriIop<F> >::IopType as IOP<F> >::verify_query(&original_poly_query.1, commitment);
            if !is_in_commitment {
                return false;
            }

            simulated_q_poly_values.push(value_at_x);
        }

        let valid = FRI::verify_proof_with_challenges(q_poly_fri_proof, domain_indexes, &simulated_q_poly_values, &fri_challenges).expect("fri verification should work");

        valid
    }

    fn verify_multiple_openings(
        &self, 
        commitments: Vec<&Self::Commitment>, 
        at_points: Vec<F>, 
        claimed_values: &Vec<F>, 
        aggregation_coefficient: F, 
        proof: &Self::OpeningProof, 
        prng: &mut Self::Prng
    ) -> bool {
        let (q_poly_fri_proof, original_poly_queries_vec) = proof;

        let lde_size = self.max_degree_plus_one.next_power_of_two() * self.lde_factor;
        let lde_domain = Domain::<F>::new_for_size(lde_size as u64).expect("large enough domain must exist");

        // first get FRI challenges

        let fri_challenges = FRI::get_fri_challenges(q_poly_fri_proof, prng);

        for c in q_poly_fri_proof.get_final_coefficients().iter() {
            prng.commit_field_element(&c);
        }

        // then make expected query locations

        let mut used_queries: Vec<usize> = vec![];

        let mut domain_indexes = vec![];

        // even while this is conditional, it can be changed to unconditional given large enough field

        while domain_indexes.len() < self.num_queries {
            let domain_idx = bytes_to_challenge_index(prng.get_challenge_bytes(), lde_size);
            let coset_index_values = < < <FRI as FriIop<F> >::IopType as IOP<F> >::Combiner as CosetCombiner<F>>::get_coset_for_natural_index(domain_idx, lde_size);
            let mut can_use = true;
            for v in coset_index_values.iter() {
                if used_queries.contains(&v) {
                    can_use = false;
                    break
                }
            }
            if can_use {
                domain_indexes.push(domain_idx);
                used_queries.extend(coset_index_values);
            }
        }

        // now simulate expected values

        let mut simulated_q_poly_values = vec![F::zero(); domain_indexes.len()];

        assert!(original_poly_queries_vec.len() == claimed_values.len());

        // accumulate value of the q poly over subpolys

        let mut alpha = F::one();

        for subpoly_index in 0..original_poly_queries_vec.len() {
            let subpoly_queries = &original_poly_queries_vec[subpoly_index];
            let claimed_value = claimed_values[subpoly_index];
            let subpoly_commitment = commitments[subpoly_index];
            let opening_at = &at_points[subpoly_index];

            let mut simulated_q_poly_subvalues = vec![];

            for (domain_idx, original_poly_query) in domain_indexes.clone().into_iter()
                                        .zip(subpoly_queries.iter()) {

                let x = lde_domain.generator.pow(&[domain_idx as u64]);

                assert!(original_poly_query.1.value() == original_poly_query.0);
            
                let mut num = original_poly_query.0;
                num.sub_assign(&claimed_value);

                let mut den = x;
                den.sub_assign(&opening_at);

                let den_inversed = den.inverse().expect("denominator is unlikely to be zero in large enough field");

                let mut value_at_x = num;
                value_at_x.mul_assign(&den_inversed);

                let is_in_commitment = < <FRI as FriIop<F> >::IopType as IOP<F> >::verify_query(&original_poly_query.1, subpoly_commitment);
                if !is_in_commitment {
                    println!("Not in the root for subpoly {} out of {}", subpoly_index, original_poly_queries_vec.len());
                    return false;
                }

                simulated_q_poly_subvalues.push(value_at_x);
            }

            // in simulated_q_poly_values now there are values of this polynomial for all the queries, 
            // now we need to sum them up with a proper coefficients starting with 0

            for (a, s) in simulated_q_poly_values.iter_mut().zip(simulated_q_poly_subvalues.iter()) {
                let mut tmp = *s;
                tmp.mul_assign(&alpha);
                a.add_assign(&tmp);
            }

            alpha.mul_assign(&aggregation_coefficient);
        }

        // println!("Will open poly at indexes {:?} for simulated values {:?}", domain_indexes, simulated_q_poly_values);

        let valid = FRI::verify_proof_with_challenges(q_poly_fri_proof, domain_indexes, &simulated_q_poly_values, &fri_challenges).expect("fri verification should work");

        valid
    }
}


// use single threaded Kate division for now
fn kate_divison_with_same_return_size<F: PrimeField>(a: &[F], mut b: F) -> Vec<F>
{
    b.negate();

    let mut q = vec![F::zero(); a.len()];

    let mut tmp = F::zero();
    let mut found_one = false;
    for (q, r) in q.iter_mut().rev().skip(1).zip(a.iter().rev()) {
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

// this one is not ZK cause will expose values not from LDE, but from the original domain too
fn bytes_to_challenge_index<S: AsRef<[u8]>>(bytes: S, lde_size: usize) -> usize {
    use byteorder::{BigEndian, ByteOrder};

    let as_ref = bytes.as_ref();
    let natural_x_index = BigEndian::read_u64(&as_ref[(as_ref.len() - 8)..]);

    let natural_x_index = natural_x_index as usize;
    let natural_x_index = natural_x_index % lde_size;

    natural_x_index
}


#[cfg(test)]
mod test {

    use super::*;
    use crate::pairing::ff::{Field, PrimeField};

    use crate::{SynthesisError};
    use std::marker::PhantomData;

    use crate::plonk::utils::*;
    use crate::plonk::commitments::transparent::fri::*;
    use crate::plonk::commitments::transparent::iop::*;
    use crate::plonk::commitments::transcript::*;
    use crate::plonk::commitments::transparent::fri::naive_fri::naive_fri::*;
    use crate::plonk::commitments::transparent::iop::blake2s_trivial_iop::*;
    use crate::plonk::commitments::*;
    

    #[test]
    fn test_small_transparent_commitment() {
        use crate::pairing::bn256::{Bn256, Fr};

        const SIZE:usize = 16;

        let worker = Worker::new();

        // let coeffs: Vec<_> = (0..SIZE).collect();
        // let coeffs: Vec<_> = vec![1, 1, 0, 0, 0, 0, 0, 0];
        let coeffs: Vec<_> = vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1];
        let coeffs = convert_to_field_elements(&coeffs, &worker);
        let poly = Polynomial::<Fr, _>::from_coeffs(coeffs).unwrap();

        let mut transcript = Blake2sTranscript::<Fr>::new();

        type Iop = TrivialBlake2sIOP<Fr>;
        type Fri = NaiveFriIop<Fr, Iop>;
        type Committer = StatelessTransparentCommitter<Fr, Fri, Blake2sTranscript<Fr>>;

        let meta = TransparentCommitterParameters {
            lde_factor: 16,
            num_queries: 2,
            output_coeffs_at_degree_plus_one: 1,
        };

        let committer = <Committer as CommitmentScheme<Fr>>::new_for_size(SIZE, meta);

        let (commitment, aux_data) = committer.commit_single(&poly);

        let open_at = Fr::from_str("123").unwrap();

        let expected_at_z = poly.evaluate_at(&worker, open_at);

        let proof = committer.open_single(&poly, open_at, expected_at_z, &aux_data.as_ref(), &mut transcript);

        let mut transcript = Blake2sTranscript::<Fr>::new();

        let valid = committer.verify_single(&commitment, open_at, expected_at_z, &proof, &mut transcript);

        assert!(valid);
    }

    #[test]
    fn test_large_transparent_commitment() {
        use std::time::Instant;
        use crate::pairing::bn256::{Bn256, Fr};

        let worker = Worker::new();

        const SIZE:usize = 1 << 20;
        // const SIZE:usize = 1 << 10;

        let coeffs: Vec<_> = (0..SIZE).collect();
        let coeffs = convert_to_field_elements(&coeffs, &worker);
        let poly = Polynomial::<Fr, _>::from_coeffs(coeffs).unwrap();

        let mut transcript = Blake2sTranscript::<Fr>::new();

        type Iop = TrivialBlake2sIOP<Fr>;
        type Fri = NaiveFriIop<Fr, Iop>;
        type Committer = StatelessTransparentCommitter<Fr, Fri, Blake2sTranscript<Fr>>;

        let meta = TransparentCommitterParameters {
            lde_factor: 16,
            num_queries: 6, // ~100 bits of security
            output_coeffs_at_degree_plus_one: 16,
        };

        let committer = <Committer as CommitmentScheme<Fr>>::new_for_size(SIZE, meta);

        let now = Instant::now();

        let (commitment, aux_data) = committer.commit_single(&poly);

        println!("Commitment taken {:?}", now.elapsed());

        let open_at = Fr::from_str("123").unwrap();

        let expected_at_z = poly.evaluate_at(&worker, open_at);

        let now = Instant::now();

        let proof = committer.open_single(&poly, open_at, expected_at_z, &aux_data.as_ref(), &mut transcript);

        println!("Opening taken {:?}", now.elapsed());

        let mut transcript = Blake2sTranscript::<Fr>::new();

        let now = Instant::now();

        let valid = committer.verify_single(&commitment, open_at, expected_at_z, &proof, &mut transcript);

        println!("Verification taken {:?}", now.elapsed());

        assert!(valid);
    }
}