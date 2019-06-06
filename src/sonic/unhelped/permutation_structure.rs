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

    pub fn print_constraints(n:usize, q: usize, coeffs: &Vec<Vec<E::Fr>>, permutations: &Vec<Vec<usize>>) {
        let m = coeffs.len();

        for constraint_idx in 1..=q {
            println!("Constraint {}", constraint_idx);
            let mut terms = vec![];
            for p_idx in 0..m {
                if let Some(variable_idx) = permutations[p_idx].iter().position(|&s| s == constraint_idx) {
                    let coeff = coeffs[p_idx][variable_idx];
                    terms.push((variable_idx, coeff));
                }
            }
            for (var_idx, coeff) in terms.into_iter() {
                if var_idx < n + 1 {
                    print!("{} * A({})", coeff, n - var_idx);
                } else if var_idx < 2*n + 1 {
                    print!("{} * B({})", coeff, var_idx - n);
                } else {
                    print!("{} * C({})", coeff, var_idx - 2*n);
                }
                print!("\n");
            }
        }
    }

    pub fn print_terms_per_variable(n:usize, q: usize, coeffs: &Vec<Vec<E::Fr>>, permutations: &Vec<Vec<usize>>) {
        let m = coeffs.len();
        let k = coeffs[0].len();

        for var_idx in 0..k {
            println!("Terms for X^{}", var_idx + 1);
            for p_idx in 0..m {
                println!("In permutation poly {}", p_idx);
                let constraint_index = permutations[p_idx][var_idx];
                if constraint_index == 0 {
                    continue;
                }
                let coeff = coeffs[p_idx][var_idx];
                if var_idx < n + 1 {
                    print!("{} * A({}) * Y^{}", coeff, n - var_idx, constraint_index);
                } else if var_idx < 2*n + 1 {
                    print!("{} * B({}) * Y^{}", coeff, var_idx - n, constraint_index);
                } else {
                    print!("{} * C({}) * Y^{}", coeff, var_idx - 2*n, constraint_index);
                }
                print!("\n");
            }
        }
    }

    pub fn print_terms_in_permutations(n:usize, q: usize, coeffs: &Vec<Vec<E::Fr>>, permutations: &Vec<Vec<usize>>) {
        let m = coeffs.len();

        for p_idx in 0..m {
            println!("Permutation polynomial {}", p_idx);
            for (var_idx, constraint_idx) in permutations[p_idx].iter().enumerate() {
                let coeff = coeffs[p_idx][var_idx];
                if var_idx < n + 1 {
                    print!("{} * A({})", coeff, n - var_idx);
                } else if var_idx < 2*n + 1 {
                    print!("{} * B({})", coeff, var_idx - n);
                } else {
                    print!("{} * C({})", coeff, var_idx - 2*n);
                }
                print!("\n");
            }
        }
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
            // these are no constant terms
            assert!(non_permuted_coeffs[i][n].is_zero());
            assert!(permutations[i][n] == 0);
        }

        for i in (0..M).into_iter().rev() {
            if !not_empty[i] {
                non_permuted_coeffs.pop();
                permutations.pop();
                m -= 1;
            }
        }

        assert!(m != 0);

        // Self::print_constraints(n, self.q, &non_permuted_coeffs, &permutations);
        // Self::print_terms_per_variable(n, self.q, &non_permuted_coeffs, &permutations);
        // Self::print_terms_in_permutations(n, self.q, &non_permuted_coeffs, &permutations);

        // for i in 0..m {
        //     println!("Coeffs = {:?}", non_permuted_coeffs[i]);
        //     println!("Permutation = {:?}", permutations[i]);
        // }

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
    -> (Vec<(E::G1Affine, E::G1Affine)>, Vec<E::Fr>, PermutationProof<E>, PermutationArgumentProof<E>, E::Fr, usize, E::Fr)
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

        // evaluate S naively

        let mut s_contrib = E::Fr::zero();
        for permutation_index in 0..m {
            for (variable_index, constraint_power) in permutations[permutation_index].iter().enumerate() {
                let y_power = y.pow([*constraint_power as u64]);
                let x_power = z.pow([(variable_index+1) as u64]);
                let coeff = non_permuted_coeffs[permutation_index][variable_index];

                let mut result = coeff;
                result.mul_assign(&x_power);
                result.mul_assign(&y_power);
                s_contrib.add_assign(&result);
            }
        }

        println!("naive s eval = {}", s_contrib);

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

        (commitments, challenges, opening, proof, z_prime, m, s_contrib)
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
            let (a, b, c) = cs.multiply(|| {
                Ok((
                    E::Fr::from_str("10").unwrap(),
                    E::Fr::from_str("20").unwrap(),
                    E::Fr::from_str("200").unwrap(),
                ))
            })?;

            cs.enforce_zero(LinearCombination::zero() + (Coeff::Full(E::Fr::from_str("2").unwrap()), a) - b);
            cs.enforce_zero(LinearCombination::zero() + (Coeff::Full(E::Fr::from_str("20").unwrap()), a) - c);
            cs.enforce_zero(LinearCombination::zero() + (Coeff::Full(E::Fr::from_str("10").unwrap()), b) - c);

            // let multiplier = cs.alloc_input(|| Ok(E::Fr::from_str("20").unwrap()))?;

            // cs.enforce_zero(LinearCombination::from(b) - multiplier);

            // let (a1, b1, _) = cs.multiply(|| {
            //     Ok((
            //         E::Fr::from_str("5").unwrap(),
            //         E::Fr::from_str("5").unwrap(),
            //         E::Fr::from_str("25").unwrap(),
            //     ))
            // })?;

            // cs.enforce_zero(LinearCombination::zero() + (Coeff::Full(E::Fr::from_str("2").unwrap()), b1) - a);
            // cs.enforce_zero(LinearCombination::zero() + (Coeff::Full(E::Fr::from_str("4").unwrap()), a1) - b);
            // cs.enforce_zero(LinearCombination::zero() + (Coeff::Full(E::Fr::from_str("40").unwrap()), b1) - c);

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

        let x: Fr = rng.gen();
        let y: Fr = rng.gen();

        let x = Fr::one();
        let mut y = Fr::one();
        y.double();

        let perm_structure = create_permutation_structure::<Bls12, _>(&MyCircuit);
        perm_structure.create_permutation_arguments(x, y, rng, &srs);
        let s2 = S2Eval::new(perm_structure.n);
        let s2 = s2.evaluate(x, y, &srs);
        let mut s2_value = s2.c_value;
        s2_value.add_assign(&s2.d_value);

        let mut expected_s2_value = Fr::zero();
        let y_inv = y.inverse().unwrap();
        let mut p1 = y;
        p1.add_assign(&y_inv);
        p1.mul_assign(&x);
        expected_s2_value.add_assign(&p1);

        let mut t0 = y;
        t0.square();

        let mut t1 = y_inv;
        t1.square();

        let mut p2 = t0;
        p2.add_assign(&t1);
        p2.mul_assign(&x);
        p2.mul_assign(&x);

        expected_s2_value.add_assign(&p2);

        println!("s2 value = {}", s2_value);
        println!("expected s2 value = {}", expected_s2_value);

        assert!(expected_s2_value == s2_value);



        println!("N = {}, Q = {}", perm_structure.n, perm_structure.q);
    }
}