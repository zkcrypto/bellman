use crate::pairing::ff::PrimeField;
use crate::plonk::commitments::transparent::iop_compiler::*;
use crate::plonk::commitments::transparent::iop_compiler::coset_combining_blake2s_tree::*;
use crate::plonk::polynomials::*;
use crate::multicore::*;
use crate::SynthesisError;
use crate::plonk::commitments::transparent::utils::log2_floor;
use crate::plonk::commitments::transcript::Prng;
use crate::plonk::commitments::transparent::precomputations::*;
use super::*;
use super::query_producer::*;

pub struct CosetCombiningFriIop<F: PrimeField> {
    cosets_schedule: Vec<usize>,
    _marker_f: std::marker::PhantomData<F>,
}

#[derive(Clone, Debug)]
pub struct CosetParams<F: PrimeField> {
    pub cosets_schedule: Vec<usize>,
    pub coset_factor: F
}

impl<F: PrimeField> FriIop<F> for CosetCombiningFriIop<F> {
    const DEGREE: usize = 2;

    type IopType = FriSpecificBlake2sTree<F>;
    type ProofPrototype = FRIProofPrototype<F, Self::IopType>;
    type Proof = FRIProof<F, Self::IopType>;
    type Params = CosetParams<F>;

    fn proof_from_lde<P: Prng<F, Input = <Self::IopType as IopInstance<F>>::Commitment>,
        C: FriPrecomputations<F>
    >(
        lde_values: &Polynomial<F, Values>, 
        lde_factor: usize,
        output_coeffs_at_degree_plus_one: usize,
        precomputations: &C,
        worker: &Worker,
        prng: &mut P,
        params: &Self::Params
    ) -> Result<Self::ProofPrototype, SynthesisError> {
        Self::proof_from_lde_by_values(
            lde_values, 
            lde_factor,
            output_coeffs_at_degree_plus_one,
            precomputations,
            worker,
            prng,
            params
        )
    }

    fn prototype_into_proof(
        prototype: Self::ProofPrototype,
        iop_values: &Polynomial<F, Values>,
        natural_first_element_indexes: Vec<usize>,
        params: &Self::Params
    ) -> Result<Self::Proof, SynthesisError> {
        prototype.produce_proof(iop_values, natural_first_element_indexes)
    }

    fn get_fri_challenges<P: Prng<F, Input = <Self::IopType as IopInstance<F>>::Commitment>>(
        proof: &Self::Proof,
        prng: &mut P,
        params: &Self::Params
    ) -> Vec<F> {
        let mut fri_challenges = vec![];

        for root in proof.roots.iter() {
            let iop_challenge = {
                prng.commit_input(&root);
                prng.get_challenge()
            };

            fri_challenges.push(iop_challenge);
        }

        fri_challenges
    }

    fn verify_proof_with_challenges(
        proof: &Self::Proof,
        natural_element_indexes: Vec<usize>,
        expected_value: &[F],
        fri_challenges: &[F],
        params: &Self::Params
    ) -> Result<bool, SynthesisError> {
        Self::verify_proof_queries(proof, natural_element_indexes, Self::DEGREE, expected_value, fri_challenges)
    }
}

use std::time::Instant;

#[derive(PartialEq, Eq, Clone)]
pub struct FRIProofPrototype<F: PrimeField, I: IopInstance<F>> {
    pub l0_commitment: I,
    pub intermediate_commitments: Vec<I>,
    pub intermediate_values: Vec< Polynomial<F, Values> >,
    pub challenges: Vec<Vec<F>>,
    pub final_root: I::Commitment,
    pub final_coefficients: Vec<F>,
    pub initial_degree_plus_one: usize,
    pub output_coeffs_at_degree_plus_one: usize,
    pub lde_factor: usize,
}

impl<F: PrimeField, I: IopInstance<F>> FriProofPrototype<F, I> for FRIProofPrototype<F, I> {
    fn get_roots(&self) -> Vec<I::Commitment> {
        let mut roots = vec![];
        // roots.push(self.l0_commitment.get_commitment().clone());
        for c in self.intermediate_commitments.iter() {
            roots.push(c.get_commitment().clone());
        }

        roots
    }

    fn get_final_root(&self) -> I::Commitment {
        self.final_root.clone()
    }

    fn get_final_coefficients(&self) -> Vec<F> {
        self.final_coefficients.clone()
    }
}

#[derive(PartialEq, Eq, Clone)]
pub struct FRIProof<F: PrimeField, I: IopInstance<F>> {
    pub queries: Vec<Vec<I::Query>>,
    pub roots: Vec<I::Commitment>,
    pub final_coefficients: Vec<F>,
    pub initial_degree_plus_one: usize,
    pub output_coeffs_at_degree_plus_one: usize,
    pub lde_factor: usize,
}

impl<F: PrimeField, I: IopInstance<F>> FriProof<F, I> for FRIProof<F, I> {
    fn get_final_coefficients(&self) -> &[F] {
        &self.final_coefficients
    }

    fn get_queries(&self) -> &Vec<Vec<I::Query>> {
        &self.queries
    }
}

impl<F: PrimeField> CosetCombiningFriIop<F> {
    pub fn proof_from_lde_by_values<P: Prng<F, Input = <<Self as FriIop<F>>::IopType as IopInstance<F>>::Commitment>,
        C: FriPrecomputations<F>
    >(
        lde_values: &Polynomial<F, Values>, 
        lde_factor: usize,
        output_coeffs_at_degree_plus_one: usize,
        precomputations: &C,
        worker: &Worker,
        prng: &mut P,
        params: &<Self as FriIop<F>>::Params
    ) -> Result<FRIProofPrototype<F, <Self as FriIop<F>>::IopType>, SynthesisError> {
        let mut coset_schedule_index = 0;
        let coset_factor = params.cosets_schedule[coset_schedule_index];

        let mut total_wrap_factor = 1;
        for s in params.cosets_schedule.iter() {
            let coeff = 1 << *s;
            total_wrap_factor *= coeff;
        }

        let mut roots = vec![];
        // let tree_params = FriSpecificBlake2sTreeParams {
        //     values_per_leaf: (1 << coset_factor)
        // };

        // let l0_commitment = FriSpecificBlake2sTree::create(lde_values.as_ref(), &tree_params);
        // let root = l0_commitment.get_commitment();
        // roots.push(root);
        let initial_domain_size = lde_values.size();

        assert_eq!(precomputations.domain_size(), initial_domain_size);

        let mut two = F::one();
        two.double();
        let two_inv = two.inverse().expect("should exist");
        
        assert!(output_coeffs_at_degree_plus_one.is_power_of_two());
        assert!(lde_factor.is_power_of_two());

        let initial_degree_plus_one = initial_domain_size / lde_factor;
        assert_eq!(initial_degree_plus_one / total_wrap_factor, output_coeffs_at_degree_plus_one, 
            "number of FRI round does not match the ouput degree: initial degree+1 =  {}, wrapping factor {}, output at degree+1 = {}",
             initial_degree_plus_one, total_wrap_factor, output_coeffs_at_degree_plus_one);

        let mut intermediate_commitments = vec![];
        let mut intermediate_values = vec![];
        let mut challenges = vec![];
        let num_challenges = coset_factor;
        let mut next_domain_challenges = {
            // prng.commit_input(&l0_commitment.get_commitment());
            let mut challenges = vec![];
            for _ in 0..num_challenges {
                challenges.push(prng.get_challenge());
            }

            challenges
        };

        challenges.push(next_domain_challenges.clone());

        let mut values_slice = lde_values.as_ref();

        let omegas_inv_bitreversed: &[F] = precomputations.omegas_inv_bitreversed();

        // if we would precompute all N we would have
        // [0, N/2, N/4, 3N/4, N/8, N/2 + N/8, N/8 + N/4, N/8 + N/4 + N/2, ...]
        // but we only precompute half of them and have
        // [0, N/4, N/8, N/8 + N/4, ...]

        let mut this_domain_size = lde_values.size();

        // step 0: fold totally by 2
        // step 1: fold totally by 4
        // etc...

        let num_steps = params.cosets_schedule.len();
        
        for (fri_step, coset_factor) in params.cosets_schedule.iter().enumerate() {
            let coset_factor = *coset_factor;
            let wrapping_factor = 1 << coset_factor;
            let next_domain_size = this_domain_size / wrapping_factor;
            let mut next_values = vec![F::zero(); next_domain_size];

            // we combine like this with FRI trees being aware of the FRI computations
            //            next_value(omega**)
            //          /                     \
            //    intermediate(omega*)       intermediate(-omega*)
            //    /           \                   /            \
            // this(omega)   this(-omega)     this(omega')    this(-omega')
            // 
            // so omega* = omega^2i. omega' = sqrt(-omega^2i) = sqrt(omega^(N/2 + 2i)) = omega^N/4 + i
            // 
            // we expect values to come bitreversed, so this(omega) and this(-omega) are always adjustent to each other
            // because in normal emumeration it would be elements b0XYZ and b1XYZ, and now it's bZYX0 and bZYX1
            // 
            // this(omega^(N/4 + i)) for b00YZ has a form b01YZ, so bitreversed it's bZY00 and bZY10
            // this(-omega^(N/4 + i)) obviously has bZY11, so they are all near in initial values

            worker.scope(next_values.len(), |scope, chunk| {
                for (i, v) in next_values.chunks_mut(chunk).enumerate() {
                    let next_domain_challenges = next_domain_challenges.clone();
                    scope.spawn(move |_| {
                        let initial_k = i*chunk;
                        let mut this_level_values = Vec::with_capacity(wrapping_factor);
                        let mut next_level_values = vec![F::zero(); wrapping_factor];
                        for (j, v) in v.iter_mut().enumerate() {
                            let batch_id = initial_k + j;
                            let values_offset = batch_id*wrapping_factor;
                            for (wrapping_step, challenge) in next_domain_challenges.iter().enumerate() {
                                let base_omega_idx = (batch_id * wrapping_factor) >> (1 + wrapping_step);
                                let expected_this_level_values = wrapping_factor >> wrapping_step;
                                let expected_next_level_values = wrapping_factor >> (wrapping_step + 1);
                                let inputs = if wrapping_step == 0 {
                                    &values_slice[values_offset..(values_offset + wrapping_factor)]
                                } else {
                                    &this_level_values[..expected_this_level_values]
                                };

                                // imagine first FRI step, first wrapping step
                                // in values we have f(i), f(i + N/2), f(i + N/4), f(i + N/4 + N/2), f(i + N/8), ...
                                // so we need to use omega(i) for the first pair, omega(i + N/4) for the second, omega(i + N/8)
                                // on the next step we would have f'(2i), f'(2i + N/2), f'(2i + N/4), f'(2i + N/4 + N/2)
                                // so we would have to pick omega(2i) and omega(2i + N/4)
                                // this means LSB is always the same an only depend on the pair_idx below
                                // MSB is more tricky
                                // for a batch number 0 we have i = 0
                                // for a batch number 1 due to bitreverse we have index equal to b000001xxx where LSB are not important in the batch
                                // such value actually gives i = bxxx100000 that is a bitreverse of the batch number with proper number of bits
                                // due to precomputed omegas also being bitreversed we just need a memory location b000001xxx >> 1

                                debug_assert_eq!(inputs.len() / 2, expected_next_level_values);

                                for (pair_idx, (pair, o)) in inputs.chunks(2).zip(next_level_values[..expected_next_level_values].iter_mut()).enumerate() {
                                    debug_assert!(base_omega_idx & pair_idx == 0);
                                    let omega_idx = base_omega_idx + pair_idx;
                                    let omega_inv = omegas_inv_bitreversed[omega_idx];
                                    let f_at_omega = pair[0];
                                    let f_at_minus_omega = pair[1];
                                    let mut v_even_coeffs = f_at_omega;
                                    v_even_coeffs.add_assign(&f_at_minus_omega);

                                    let mut v_odd_coeffs = f_at_omega;
                                    v_odd_coeffs.sub_assign(&f_at_minus_omega);
                                    v_odd_coeffs.mul_assign(&omega_inv);

                                    let mut tmp = v_odd_coeffs;
                                    tmp.mul_assign(&challenge);
                                    tmp.add_assign(&v_even_coeffs);
                                    tmp.mul_assign(&two_inv);

                                    *o = tmp;
                                }

                                this_level_values.clear();
                                this_level_values.clone_from(&next_level_values);
                            }

                            *v = next_level_values[0];
                        }
                    });
                }
            });

            if fri_step < num_steps - 1 {
                coset_schedule_index += 1;
                this_domain_size = next_domain_size;
                let coset_factor = params.cosets_schedule[coset_schedule_index];
                let tree_params = FriSpecificBlake2sTreeParams {
                    values_per_leaf: (1 << coset_factor)
                };
                let intermediate_iop = FriSpecificBlake2sTree::create(next_values.as_ref(), &tree_params);
                let root = intermediate_iop.get_commitment();
                roots.push(root);
                let num_challenges = coset_factor;
                next_domain_challenges = {
                    prng.commit_input(&intermediate_iop.get_commitment());
                    let mut challenges = vec![];
                    for _ in 0..num_challenges {
                        challenges.push(prng.get_challenge());
                    }

                    challenges
                };

                challenges.push(next_domain_challenges.clone());
                intermediate_commitments.push(intermediate_iop);
            } 

            let next_values_as_poly = Polynomial::from_values(next_values)?;
            intermediate_values.push(next_values_as_poly);

            values_slice = intermediate_values.last().expect("is something").as_ref();      
        }

        let final_root = roots.last().expect("will work").clone();

        assert_eq!(challenges.len(), num_steps);
        // assert_eq!(roots.len(), num_steps);
        assert_eq!(intermediate_commitments.len(), num_steps-1);
        assert_eq!(intermediate_values.len(), num_steps);

        let mut final_poly_values = Polynomial::from_values(values_slice.to_vec())?;
        final_poly_values.bitreverse_enumeration(&worker);
        let final_poly_coeffs = if params.coset_factor == F::one() {
            final_poly_values.icoset_fft(&worker)
        } else {
            final_poly_values.icoset_fft_for_generator(&worker, &params.coset_factor)
        };

        let mut final_poly_coeffs = final_poly_coeffs.into_coeffs();

        let mut degree = final_poly_coeffs.len() - 1;
        for c in final_poly_coeffs.iter().rev() {
            if c.is_zero() {
                degree -= 1;
            } else {
                break
            }
        }

        assert!(degree < output_coeffs_at_degree_plus_one, "polynomial degree is too large, coeffs = {:?}", final_poly_coeffs);

        final_poly_coeffs.truncate(output_coeffs_at_degree_plus_one);

        Ok(FRIProofPrototype {
            // l0_commitment,
            intermediate_commitments,
            intermediate_values,
            challenges,
            final_root,
            final_coefficients: final_poly_coeffs,
            initial_degree_plus_one,
            output_coeffs_at_degree_plus_one,
            lde_factor,
        })

    }
}

#[cfg(test)]
mod test {
    #[test]
    fn test_bench_fri_with_coset_combining() {
        use crate::ff::Field;
        use crate::ff::PrimeField;
        use rand::{XorShiftRng, SeedableRng, Rand, Rng};
        use crate::plonk::transparent_engine::proth_engine::Fr;
        use crate::plonk::transparent_engine::PartialTwoBitReductionField;
        use crate::plonk::polynomials::*;
        use std::time::Instant;
        use crate::multicore::*;
        use crate::plonk::commitments::transparent::utils::*;
        use crate::plonk::fft::cooley_tukey_ntt::{CTPrecomputations, BitReversedOmegas};
        use crate::plonk::commitments::transparent::fri::coset_combining_fri::FriPrecomputations;
        use crate::plonk::commitments::transparent::fri::coset_combining_fri::fri::*;
        use crate::plonk::commitments::transparent::fri::coset_combining_fri::precomputation::OmegasInvBitreversed;
        use crate::plonk::commitments::transcript::*;

        const SIZE: usize = 1024;

        let mut transcript = Blake2sTranscript::<Fr>::new();

        let worker = Worker::new_with_cpus(1);

        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let coeffs = (0..SIZE).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
    
        let poly = Polynomial::<Fr, _>::from_coeffs(coeffs).unwrap();
        let precomp = BitReversedOmegas::<Fr>::new_for_domain_size(poly.size());
        let start = Instant::now();
        let coset_factor = Fr::multiplicative_generator();
        let eval_result = poly.bitreversed_lde_using_bitreversed_ntt(&worker, 16, &precomp, &coset_factor).unwrap();
        println!("LDE with factor 16 for size {} bitreversed {:?}", SIZE, start.elapsed());

        let fri_precomp = <OmegasInvBitreversed::<Fr> as FriPrecomputations<Fr>>::new_for_domain_size(eval_result.size());

        let params = CosetParams::<Fr> {
            cosets_schedule: vec![3, 3, 3],
            coset_factor: coset_factor
        };

        let fri_proto = CosetCombiningFriIop::<Fr>::proof_from_lde(
            &eval_result, 
            16, 
            2, 
            &fri_precomp, 
            &worker, 
            &mut transcript,
            &params
        ).expect("FRI must succeed");
    }

    #[test]
    #[should_panic]
    fn test_invalid_eval_fri_with_coset_combining() {
        use crate::ff::Field;
        use crate::ff::PrimeField;
        use rand::{XorShiftRng, SeedableRng, Rand, Rng};
        use crate::plonk::transparent_engine::proth_engine::Fr;
        use crate::plonk::transparent_engine::PartialTwoBitReductionField;
        use crate::plonk::polynomials::*;
        use std::time::Instant;
        use crate::multicore::*;
        use crate::plonk::commitments::transparent::utils::*;
        use crate::plonk::fft::cooley_tukey_ntt::{CTPrecomputations, BitReversedOmegas};
        use crate::plonk::commitments::transparent::fri::coset_combining_fri::FriPrecomputations;
        use crate::plonk::commitments::transparent::fri::coset_combining_fri::fri::*;
        use crate::plonk::commitments::transparent::fri::coset_combining_fri::precomputation::OmegasInvBitreversed;
        use crate::plonk::commitments::transcript::*;

        const SIZE: usize = 1024;

        let mut transcript = Blake2sTranscript::<Fr>::new();

        let worker = Worker::new_with_cpus(1);

        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let coeffs = (0..SIZE).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
    
        let poly = Polynomial::<Fr, _>::from_coeffs(coeffs).unwrap();
        let precomp = BitReversedOmegas::<Fr>::new_for_domain_size(poly.size());
        let start = Instant::now();
        let coset_factor = Fr::multiplicative_generator();
        let mut eval_result = poly.bitreversed_lde_using_bitreversed_ntt(&worker, 16, &precomp, &coset_factor).unwrap();
        eval_result.as_mut()[1].sub_assign(&Fr::one());
        println!("LDE with factor 16 for size {} bitreversed {:?}", SIZE, start.elapsed());

        let fri_precomp = <OmegasInvBitreversed::<Fr> as FriPrecomputations<Fr>>::new_for_domain_size(eval_result.size());

        let params = CosetParams::<Fr> {
            cosets_schedule: vec![3, 3, 3],
            coset_factor: coset_factor
        };

        let fri_proto = CosetCombiningFriIop::<Fr>::proof_from_lde(
            &eval_result, 
            16, 
            2, 
            &fri_precomp, 
            &worker, 
            &mut transcript,
            &params
        ).expect("FRI must succeed");
    }
}