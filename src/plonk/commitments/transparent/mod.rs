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
    precomputed_values: FRI::Precomputations,
    _marker_t: std::marker::PhantomData<T>
}

pub struct TransparentCommitterParameters {
    lde_factor: usize,
    num_queries: usize,
    output_coeffs_at_degree_plus_one: usize,
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
        let precomputations = <FRI::Precomputations as FriPrecomputations<F>>::new_for_domain_size(lde_domain_size);

        StatelessTransparentCommitter::<F, FRI, T> {
            max_degree_plus_one: max_degree_plus_one,
            lde_factor: meta.lde_factor,
            output_coeffs_at_degree_plus_one: meta.output_coeffs_at_degree_plus_one,
            num_queries: meta.num_queries,
            worker: Worker::new(),
            precomputed_values: precomputations,
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

        let division_result = kate_divison_with_same_return_size(poly.as_ref(), opening_value);
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

        let mut used_queries = vec![];

        let mut element_indexes = vec![];

        while used_queries.len() < self.num_queries {
            let domain_idx = bytes_to_challenge_index(prng.get_challenge_bytes(), lde_size, self.lde_factor);
            let coset_values = < < <FRI as FriIop<F> >::IopType as IOP<F> >::Combiner as CosetCombiner<F>>::get_coset_for_natural_index(domain_idx, lde_size);
            used_queries.extend(coset_values);
            if !used_queries.contains(&domain_idx) {
                element_indexes.push(domain_idx);
            }
        }

        let q_poly_fri_proof = FRI::prototype_into_proof(fri_proto, &q_poly_lde, element_indexes.clone()).expect("must generate a proper proof");

        let mut original_poly_queries = vec![];
        
        let (original_poly_lde, original_poly_lde_oracle) = data;
        for idx in element_indexes.into_iter() {
            let original_value = original_poly_lde.as_ref()[idx];
            let original_poly_query = original_poly_lde_oracle.query(idx, original_poly_lde.as_ref());
            original_poly_queries.push((original_value, original_poly_query));
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

fn bytes_to_challenge_index<S: AsRef<[u8]>>(bytes: S, lde_size: usize, lde_factor: usize) -> usize {
    use byteorder::{BigEndian, ByteOrder};

    let as_ref = bytes.as_ref();
    let natural_x_index = BigEndian::read_u64(&as_ref[(as_ref.len() - 8)..]);

    let natural_x_index = natural_x_index as usize;
    let mut natural_x_index = natural_x_index % lde_size;

    natural_x_index
}