use crate::pairing::ff::{Field};
use crate::pairing::{Engine, CurveProjective};
use std::marker::PhantomData;

use crate::sonic::helped::{Proof, SxyAdvice};
use crate::sonic::helped::batch::Batch;
use crate::sonic::helped::poly::{SxEval, SyEval};
use crate::sonic::helped::Parameters;

use crate::SynthesisError;

use crate::sonic::transcript::{Transcript, TranscriptProtocol};
use crate::sonic::util::*;
use crate::sonic::cs::{Backend, SynthesisDriver, ConstraintSystem};
use crate::sonic::cs::{Circuit, Variable, Coeff};
use crate::sonic::srs::SRS;
use crate::sonic::sonic::Preprocess;
use crate::sonic::sonic::M;
use crate::sonic::sonic::PermutationSynthesizer;

use super::s2_proof::*;
use super::permutation_argument::*;

#[derive(Clone)]
pub struct PermutationStructure<E: Engine> {
    pub n: usize,
    pub q: usize,
    pub a: Vec<[Option<(Coeff<E>, usize)>; M]>,
    pub b: Vec<[Option<(Coeff<E>, usize)>; M]>,
    pub c: Vec<[Option<(Coeff<E>, usize)>; M]>,
}

pub fn create_permutation_structure<E: Engine, C: Circuit<E>>(
    circuit: &C,
) -> PermutationStructure<E>
{
    let mut backend: Preprocess<E> = Preprocess::new();

    let (a, b, c) = {

        let mut cs: PermutationSynthesizer<E, &'_ mut Preprocess<E>> = PermutationSynthesizer::new(&mut backend);

        let one = cs.alloc_input(|| Ok(E::Fr::one())).expect("should have no issues");

        match (one, <PermutationSynthesizer<E, &'_ mut Preprocess<E>> as ConstraintSystem<E>>::ONE) {
            (Variable::A(1), Variable::A(1)) => {},
            _ => panic!("one variable is incorrect")
        }

        circuit.synthesize(&mut cs).expect("should synthesize");


        (cs.a, cs.b, cs.c)
    };

    let n = backend.n;
    let q = backend.q;

    println!("Will have {} gates and {} linear constraints", n, q);

    PermutationStructure::<E> {
        n: n,
        q: q,
        a: a,
        b: b,
        c: c
    }
}

use rand::{Rng, Rand};

impl<E: Engine> PermutationStructure<E> {
    pub fn calculate_s2_commitment_value(&self, srs: &SRS<E>) -> E::G1Affine {
        S2Eval::calculate_commitment_element(self.n, srs)
    }

    pub fn calculate_s2_proof(&self, x: E::Fr, y: E::Fr, srs: &SRS<E>) -> S2Proof<E> {
        let s2_eval = S2Eval::new(self.n);

        s2_eval.evaluate(x, y, &srs)
    }

    fn create_permutation_vectors(&self) -> (Vec<Vec<E::Fr>>, Vec<Vec<usize>>) {
        // we have to form non-permuted coefficients, as well as permutation structures;
        let n = self.n;
        let mut non_permuted_coeffs = vec![vec![E::Fr::zero(); 3*n+1]; M];
        let mut permutations = vec![vec![0usize; 3*n+1]; M];

        let one = E::Fr::one();
        let mut minus_one = E::Fr::one();
        minus_one.negate();

        let mut not_empty = [false; M];
        // go other the permutations
        for (gate_index, info) in self.a.iter().enumerate() {
            let offset = n-1;
            for i in 0..M {
                // coefficients of A are placed at the offset = 0 from the beginning of the vector
                if let Some((coeff, place)) = info[i].as_ref() {
                    // place it
                    assert!(*place != 0);
                    let x_power = offset - gate_index + 1;
                    let array_position = offset - gate_index; // special for A
                    let place_coeff_into = &mut non_permuted_coeffs[i];
                    let place_permutation_into = &mut permutations[i];
                    match coeff {
                        Coeff::Zero => {
                        },
                        Coeff::One => {
                            not_empty[i] = true;
                            place_coeff_into[array_position] = one; 
                            place_permutation_into[array_position] = *place;
                        },
                        Coeff::NegativeOne => {
                            not_empty[i] = true;
                            place_coeff_into[array_position] = minus_one; 
                            place_permutation_into[array_position] = *place;
                        },
                        Coeff::Full(value) => {
                            not_empty[i] = true;
                            place_coeff_into[array_position] = *value; 
                            place_permutation_into[array_position] = *place;
                        }
                    }
                }
            }
        }

        for (gate_index, info) in self.b.iter().enumerate() {
            let offset = n + 1;
            for i in 0..M {
                if let Some((coeff, place)) = info[i].as_ref() {
                    // place it
                    assert!(*place != 0);
                    let x_power = offset + gate_index + 1; // 1 indexed
                    let array_position = offset + gate_index;
                    let place_coeff_into = &mut non_permuted_coeffs[i];
                    let place_permutation_into = &mut permutations[i];
                    match coeff {
                        Coeff::Zero => {
                        },
                        Coeff::One => {
                            not_empty[i] = true;
                            place_coeff_into[array_position] = one; 
                            place_permutation_into[array_position] = *place;
                        },
                        Coeff::NegativeOne => {
                            not_empty[i] = true;
                            place_coeff_into[array_position] = minus_one; 
                            place_permutation_into[array_position] = *place;
                        },
                        Coeff::Full(value) => {
                            not_empty[i] = true;
                            place_coeff_into[array_position] = *value; 
                            place_permutation_into[array_position] = *place;
                        }
                    }
                }
            }
        }

        for (gate_index, info) in self.c.iter().enumerate() {
            let offset = 2*n + 1;
            for i in 0..M {
                // coefficients of A are placed at the offset = 0 from the beginning of the vector
                if let Some((coeff, place)) = info[i].as_ref() {
                    // place it
                    assert!(*place != 0);
                    let x_power = offset + gate_index + 1; // 1 indexed
                    let array_position = offset + gate_index;
                    let place_coeff_into = &mut non_permuted_coeffs[i];
                    let place_permutation_into = &mut permutations[i];
                    match coeff {
                        Coeff::Zero => {
                        },
                        Coeff::One => {
                            not_empty[i] = true;
                            place_coeff_into[array_position] = one; 
                            place_permutation_into[array_position] = *place;
                        },
                        Coeff::NegativeOne => {
                            not_empty[i] = true;
                            place_coeff_into[array_position] = minus_one; 
                            place_permutation_into[array_position] = *place;
                        },
                        Coeff::Full(value) => {
                            not_empty[i] = true;
                            place_coeff_into[array_position] = *value; 
                            place_permutation_into[array_position] = *place;
                        }
                    }
                }
            }
        }

        // need to fill arrays with non-zero indexes just to have full permutation, even while it's just zero coefficient

        // TODO: fix

        let mut m = M;

        for i in (0..M).into_iter().rev() {
            if !not_empty[i] {
                non_permuted_coeffs.pop();
                permutations.pop();
                m -= 1;
            }
        }

        assert!(m != 0);

        // find something faster, although it's still linear

        for i in 0..m {
            let mut fillers: Vec<usize> = (1..=(3*n+1)).map(|el| el).collect();
            for (p, c) in permutations[i].iter_mut().zip(non_permuted_coeffs[i].iter()) {
                if *p == 0 {
                    assert!(c.is_zero());
                } else {
                    fillers[*p - 1] = 0;
                }
            }
            let mut fill_from = 0;
            for p in permutations[i].iter_mut() {
                if *p == 0 {
                    loop {
                        if fillers[fill_from] != 0 {
                            *p = fillers[fill_from];
                            fill_from += 1;
                            break;
                        } else {
                            fill_from += 1;
                        }
                    }
                }
            }
        }

        (non_permuted_coeffs, permutations)
    }

    pub fn create_permutation_special_reference(&self, srs: &SRS<E>) -> SpecializedSRS<E>
    {
        let (non_permuted_coeffs, permutations) = self.create_permutation_vectors();

        let specialized_srs = PermutationArgument::make_specialized_srs(
            &non_permuted_coeffs, 
            &permutations, 
            &srs
        );

        specialized_srs
    }

    pub fn create_permutation_arguments<R: Rng>(&self, y: E::Fr, z: E::Fr, rng: &mut R, srs: &SRS<E>) 
    -> (Vec<(E::G1Affine, E::G1Affine)>, Vec<E::Fr>, PermutationProof<E>, PermutationArgumentProof<E>, E::Fr, usize)
    {
        // we have to form non-permuted coefficients, as well as permutation structures;
        let n = self.n;
        
        let (non_permuted_coeffs, permutations) = self.create_permutation_vectors();

        let m = non_permuted_coeffs.len();

        println!("Will need {} permutation polynomials", m);

        let specialized_srs = PermutationArgument::make_specialized_srs(
            &non_permuted_coeffs, 
            &permutations, 
            &srs
        );

        let mut argument = PermutationArgument::new(non_permuted_coeffs, permutations);
        let challenges = (0..m).map(|_| E::Fr::rand(rng)).collect::<Vec<_>>();

        let commitments = argument.commit(y, &srs);
        let mut s_commitments = vec![];
        let mut s_prime_commitments = vec![];
        for (s, s_prime) in commitments.clone().into_iter() {
            s_commitments.push(s);
            // println!("S' = {}", s_prime);
            s_prime_commitments.push(s_prime);

        }

        let z_prime : E::Fr = rng.gen();

        let opening = argument.open_commitments_to_s_prime(&challenges, y, z_prime, &srs);

        let randomness = (0..2).map(|_| E::Fr::rand(rng)).collect::<Vec<_>>();

        let valid = PermutationArgument::verify_s_prime_commitment(n, 
            &randomness, 
            &challenges, 
            &s_prime_commitments, 
            &opening, 
            y, 
            z_prime, 
            &specialized_srs, 
            &srs);

        assert!(valid, "s' commitment must be valid");

        let beta : E::Fr = rng.gen();
        let gamma : E::Fr = rng.gen();

        let grand_product_challenges = (0..m).map(|_| E::Fr::rand(rng)).collect::<Vec<_>>();
        let wellformed_challenges = (0..(2*m)).map(|_| E::Fr::rand(rng)).collect::<Vec<_>>();

        let proof = argument.make_argument(
            beta, 
            gamma, 
            & grand_product_challenges, 
            & wellformed_challenges, 
            y, 
            z, 
            &specialized_srs, &srs);

        let valid = PermutationArgument::verify(&s_commitments, &proof, z, &srs);

        assert!(valid, "permutation argument must be valid");

        (commitments, challenges, opening, proof, z_prime, m)
    }
}

#[test]
fn test_simple_succinct_sonic() {
    use crate::pairing::ff::{Field, PrimeField};
    use crate::pairing::{Engine, CurveAffine, CurveProjective};
    use crate::pairing::bls12_381::{Bls12, Fr};
    use std::time::{Instant};
    use crate::sonic::srs::SRS;
    use crate::sonic::cs::{Circuit, ConstraintSystem, LinearCombination};

    struct MyCircuit;

    impl<E: Engine> Circuit<E> for MyCircuit {
        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            let (a, b, _) = cs.multiply(|| {
                Ok((
                    E::Fr::from_str("10").unwrap(),
                    E::Fr::from_str("20").unwrap(),
                    E::Fr::from_str("200").unwrap(),
                ))
            })?;

            cs.enforce_zero(LinearCombination::zero() + (Coeff::Full(E::Fr::from_str("2").unwrap()), a) - b);

            let multiplier = cs.alloc_input(|| Ok(E::Fr::from_str("20").unwrap()))?;

            cs.enforce_zero(LinearCombination::from(b) - multiplier);

            Ok(())
        }
    }

    let srs_x = Fr::from_str("23923").unwrap();
    let srs_alpha = Fr::from_str("23728792").unwrap();
    println!("making srs");
    let start = Instant::now();
    let srs = SRS::<Bls12>::dummy(830564, srs_x, srs_alpha);
    println!("done in {:?}", start.elapsed());

    {
        use rand::{XorShiftRng, SeedableRng, Rand, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        
        use crate::sonic::sonic::Basic;
        use crate::sonic::sonic::AdaptorCircuit;
        use crate::sonic::helped::prover::{create_advice_on_srs, create_proof_on_srs};
        use crate::sonic::helped::{MultiVerifier, get_circuit_parameters_for_succinct_sonic};
        use crate::sonic::helped::helper::{create_aggregate_on_srs};
        use crate::sonic::sonic::Permutation3;
        use crate::sonic::unhelped::permutation_structure::*;

        let perm_structure = create_permutation_structure::<Bls12, _>(&MyCircuit);
        perm_structure.create_permutation_arguments(Fr::one(), Fr::one(), rng, &srs);

        println!("N = {}, Q = {}", perm_structure.n, perm_structure.q);
    }
}