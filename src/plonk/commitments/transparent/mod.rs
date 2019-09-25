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
    precomputed_values: PrecomputedInvOmegas<F>,
    _marker_fri: std::marker::PhantomData<FRI>,
    _marker_t: std::marker::PhantomData<T>
}

pub struct TransparentCommitterParameters {
    pub lde_factor: usize,
    pub num_queries: usize,
    pub output_coeffs_at_degree_plus_one: usize,
}

impl<
    F: PrimeField, 
    FRI: FriIop<F>,
    T: Transcript<F, Input = < < < <FRI as FriIop<F> >::IopType as IOP<F> >::Tree as IopTree<F> >::TreeHasher as IopTreeHasher<F>>::HashOutput >
> CommitmentScheme<F> for StatelessTransparentCommitter<F, FRI, T> {
    type Commitment = < < < <FRI as FriIop<F> >::IopType as IOP<F> >::Tree as IopTree<F> >::TreeHasher as IopTreeHasher<F>>::HashOutput;
    // type OpeningProof = Vec< < < <FRI as FriIop<F> >::IopType as IOP<F> >::Tree as IopTree<F> >::Query >;
    type OpeningProof = (FRI::Proof, Vec< (F, < < FRI as FriIop<F> >::IopType as IOP<F> >::Query) > );
    type IntermediateData = (Polynomial<F, Values>, < FRI as FriIop<F> >::IopType);
    type Meta = TransparentCommitterParameters;
    type Prng = T;

    // <T: Transcript<F>, Input = < < I::Tree as IopTree<F> >::TreeHasher as IopTreeHasher<F> >::HashOutput> 

    fn new_for_size(max_degree_plus_one: usize, meta: Self::Meta) -> Self {
        let base_size = max_degree_plus_one.next_power_of_two();
        assert!(meta.lde_factor.is_power_of_two());
        assert!(meta.output_coeffs_at_degree_plus_one.is_power_of_two());
        let lde_domain_size = base_size*meta.lde_factor;
        let lde_domain = Domain::<F>::new_for_size(lde_domain_size as u64).expect("domain of large enough size should exist");
        let worker = Worker::new();
        let precomputations = PrecomputedInvOmegas::<F>::new_for_domain(&lde_domain, &worker);

        StatelessTransparentCommitter::<F, FRI, T> {
            max_degree_plus_one: max_degree_plus_one,
            lde_factor: meta.lde_factor,
            output_coeffs_at_degree_plus_one: meta.output_coeffs_at_degree_plus_one,
            num_queries: meta.num_queries,
            worker: worker,
            precomputed_values: precomputations,
            _marker_fri: std::marker::PhantomData,
            _marker_t: std::marker::PhantomData
        }
    }

    fn commit_single(&self, poly: &Polynomial<F, Coefficients>) -> (Self::Commitment, Self::IntermediateData) {
        let original_poly_lde = poly.clone().lde(&self.worker, self.lde_factor).expect("must make an LDE");
        let original_tree = < < FRI as FriIop<F> >::IopType as IOP<F> >::create(&original_poly_lde.as_ref());
        let commitment = original_tree.get_root();

        (commitment, (original_poly_lde, original_tree))
        
    }

    fn commit_multiple(&self, polynomials: Vec<&Polynomial<F, Coefficients>>, degrees: Vec<usize>, aggregation_coefficient: F) -> (Self::Commitment, Vec<Self::IntermediateData>) {
        unimplemented!()
    }

    fn open_single(&self, poly: &Polynomial<F, Coefficients>, at_point: F, data: Self::IntermediateData, prng: &mut Self::Prng) -> (F, Self::OpeningProof) {
        let opening_value = poly.evaluate_at(&self.worker, at_point);

        let division_result = {
            let mut q_poly_proto = poly.clone();
            q_poly_proto.as_mut()[0].sub_assign(&opening_value);
            let division_result = kate_divison_with_same_return_size(q_poly_proto.as_ref(), at_point);

            division_result
        };

        let q_poly = Polynomial::<F, Coefficients>::from_coeffs(division_result).expect("must be small enough");
        let q_poly_lde = q_poly.lde(&self.worker, self.lde_factor).expect("must make an LDE");

        let lde_size = q_poly_lde.size();

        let fri_proto = FRI::proof_from_lde(
            &q_poly_lde, 
            self.lde_factor, 
            self.output_coeffs_at_degree_plus_one, 
            &self.precomputed_values, 
            &self.worker, 
            prng
        ).expect("FRI must succeed");

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

        let (original_poly_lde, original_poly_lde_oracle) = data;
        for idx in domain_indexes.into_iter() {
            let original_value = < < <FRI as FriIop<F> >::IopType as IOP<F> >::Combiner as CosetCombiner<F>>::get_for_natural_index(original_poly_lde.as_ref(), idx);
            let original_poly_query = original_poly_lde_oracle.query(idx, original_poly_lde.as_ref());
            original_poly_queries.push((*original_value, original_poly_query));
        }

        (opening_value, (q_poly_fri_proof, original_poly_queries))

    }
    fn open_multiple(
        &self, 
        polynomials: Vec<&Polynomial<F, Coefficients>>, 
        degrees: Vec<usize>, 
        aggregation_coefficient: F, 
        at_point: F, 
        data: Vec<Self::IntermediateData>, 
        prng: &mut Self::Prng
    ) -> (Vec<F>, Self::OpeningProof) {
        unimplemented!()
    }

    fn verify_single(&self, commitment: &Self::Commitment, at_point: F, claimed_value: F, proof: &Self::OpeningProof, prng: &mut Self::Prng) -> bool {
        let (q_poly_fri_proof, original_poly_queries) = proof;

        let lde_size = self.max_degree_plus_one.next_power_of_two() * self.lde_factor;
        let lde_domain = Domain::<F>::new_for_size(lde_size as u64).expect("large enough domain must exist");

        // first get FRI challenges

        let fri_challenges = FRI::get_fri_challenges(q_poly_fri_proof, prng);

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
        println!("Claiming {} at {}", claimed_value, at_point);

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

        println!("All initial oracle queries are fine");

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

        let (opening, proof) = committer.open_single(&poly, open_at, aux_data, &mut transcript);

        assert!(opening == expected_at_z);

        let mut transcript = Blake2sTranscript::<Fr>::new();

        let valid = committer.verify_single(&commitment, open_at, opening, &proof, &mut transcript);

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

        let (opening, proof) = committer.open_single(&poly, open_at, aux_data, &mut transcript);

        println!("Opening taken {:?}", now.elapsed());

        assert!(opening == expected_at_z);

        let mut transcript = Blake2sTranscript::<Fr>::new();

        let now = Instant::now();

        let valid = committer.verify_single(&commitment, open_at, opening, &proof, &mut transcript);

        println!("Verification taken {:?}", now.elapsed());

        assert!(valid);
    }
}