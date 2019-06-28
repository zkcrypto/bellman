extern crate rand;

// For randomness (during paramgen and proof generation)
use rand::{thread_rng, Rng};

// For benchmarking
use std::time::{Duration, Instant};

// Bring in some tools for using pairing-friendly curves
use crate::pairing::{
    Engine  
};

use crate::pairing::ff::{
    Field,
};

// We're going to use the BLS12-381 pairing-friendly elliptic curve.
use crate::pairing::bls12_381::{
    Bls12
};

use crate::pairing::bn256::{
    Bn256
};

// We'll use these interfaces to construct our circuit.
use crate::{
    Circuit,
    ConstraintSystem,
    SynthesisError
};

// const MIMC_ROUNDS: usize = 322;

const MIMC_ROUNDS: usize = 1000000;

fn mimc<E: Engine>(
    mut xl: E::Fr,
    mut xr: E::Fr,
    constants: &[E::Fr]
) -> E::Fr
{
    assert_eq!(constants.len(), MIMC_ROUNDS);

    for i in 0..MIMC_ROUNDS {
        let mut tmp1 = xl;
        tmp1.add_assign(&constants[i]);
        let mut tmp2 = tmp1;
        tmp2.square();
        tmp2.mul_assign(&tmp1);
        tmp2.add_assign(&xr);
        xr = xl;
        xl = tmp2;
    }

    xl
}

/// This is our demo circuit for proving knowledge of the
/// preimage of a MiMC hash invocation.
#[derive(Clone)]
struct MiMCDemo<'a, E: Engine> {
    xl: Option<E::Fr>,
    xr: Option<E::Fr>,
    constants: &'a [E::Fr]
}

/// Our demo circuit implements this `Circuit` trait which
/// is used during paramgen and proving in order to
/// synthesize the constraint system.
impl<'a, E: Engine> Circuit<E> for MiMCDemo<'a, E> {
    fn synthesize<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<(), SynthesisError>
    {
        assert_eq!(self.constants.len(), MIMC_ROUNDS);

        // Allocate the first component of the preimage.
        let mut xl_value = self.xl;
        let mut xl = cs.alloc(|| "preimage xl", || {
            xl_value.ok_or(SynthesisError::AssignmentMissing)
        })?;

        // Allocate the second component of the preimage.
        let mut xr_value = self.xr;
        let mut xr = cs.alloc(|| "preimage xr", || {
            xr_value.ok_or(SynthesisError::AssignmentMissing)
        })?;

        for i in 0..MIMC_ROUNDS {
            // xL, xR := xR + (xL + Ci)^3, xL
            let cs = &mut cs.namespace(|| format!("round {}", i));

            // tmp = (xL + Ci)^2
            let tmp_value = xl_value.map(|mut e| {
                e.add_assign(&self.constants[i]);
                e.square();
                e
            });
            let tmp = cs.alloc(|| "tmp", || {
                tmp_value.ok_or(SynthesisError::AssignmentMissing)
            })?;

            cs.enforce(
                || "tmp = (xL + Ci)^2",
                |lc| lc + xl + (self.constants[i], CS::one()),
                |lc| lc + xl + (self.constants[i], CS::one()),
                |lc| lc + tmp
            );

            // new_xL = xR + (xL + Ci)^3
            // new_xL = xR + tmp * (xL + Ci)
            // new_xL - xR = tmp * (xL + Ci)
            let new_xl_value = xl_value.map(|mut e| {
                e.add_assign(&self.constants[i]);
                e.mul_assign(&tmp_value.unwrap());
                e.add_assign(&xr_value.unwrap());
                e
            });

            let new_xl = if i == (MIMC_ROUNDS-1) {
                // This is the last round, xL is our image and so
                // we allocate a public input.
                cs.alloc_input(|| "image", || {
                    new_xl_value.ok_or(SynthesisError::AssignmentMissing)
                })?
            } else {
                cs.alloc(|| "new_xl", || {
                    new_xl_value.ok_or(SynthesisError::AssignmentMissing)
                })?
            };

            cs.enforce(
                || "new_xL = xR + (xL + Ci)^3",
                |lc| lc + tmp,
                |lc| lc + xl + (self.constants[i], CS::one()),
                |lc| lc + new_xl - xr
            );

            // xR = xL
            xr = xl;
            xr_value = xl_value;

            // xL = new_xL
            xl = new_xl;
            xl_value = new_xl_value;
        }

        Ok(())
    }
}

/// This is our demo circuit for proving knowledge of the
/// preimage of a MiMC hash invocation.
#[derive(Clone)]
struct MiMCDemoNoInputs<'a, E: Engine> {
    xl: Option<E::Fr>,
    xr: Option<E::Fr>,
    image: Option<E::Fr>,
    constants: &'a [E::Fr]
}

/// Our demo circuit implements this `Circuit` trait which
/// is used during paramgen and proving in order to
/// synthesize the constraint system.
impl<'a, E: Engine> Circuit<E> for MiMCDemoNoInputs<'a, E> {
    fn synthesize<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<(), SynthesisError>
    {
        assert_eq!(self.constants.len(), MIMC_ROUNDS);

        // Allocate the first component of the preimage.
        let mut xl_value = self.xl;
        let mut xl = cs.alloc(|| "preimage xl", || {
            xl_value.ok_or(SynthesisError::AssignmentMissing)
        })?;

        // Allocate the second component of the preimage.
        let mut xr_value = self.xr;
        let mut xr = cs.alloc(|| "preimage xr", || {
            xr_value.ok_or(SynthesisError::AssignmentMissing)
        })?;

        for i in 0..MIMC_ROUNDS {
            // xL, xR := xR + (xL + Ci)^3, xL
            let cs = &mut cs.namespace(|| format!("round {}", i));

            // tmp = (xL + Ci)^2
            let tmp_value = xl_value.map(|mut e| {
                e.add_assign(&self.constants[i]);
                e.square();
                e
            });
            let tmp = cs.alloc(|| "tmp", || {
                tmp_value.ok_or(SynthesisError::AssignmentMissing)
            })?;

            cs.enforce(
                || "tmp = (xL + Ci)^2",
                |lc| lc + xl + (self.constants[i], CS::one()),
                |lc| lc + xl + (self.constants[i], CS::one()),
                |lc| lc + tmp
            );

            // new_xL = xR + (xL + Ci)^3
            // new_xL = xR + tmp * (xL + Ci)
            // new_xL - xR = tmp * (xL + Ci)
            let new_xl_value = xl_value.map(|mut e| {
                e.add_assign(&self.constants[i]);
                e.mul_assign(&tmp_value.unwrap());
                e.add_assign(&xr_value.unwrap());
                e
            });

            let new_xl = if i == (MIMC_ROUNDS-1) {
                // This is the last round, xL is our image and so
                // we use the image
                let image_value = self.image;
                cs.alloc(|| "image", || {
                    image_value.ok_or(SynthesisError::AssignmentMissing)
                })?
            } else {
                cs.alloc(|| "new_xl", || {
                    new_xl_value.ok_or(SynthesisError::AssignmentMissing)
                })?
            };

            cs.enforce(
                || "new_xL = xR + (xL + Ci)^3",
                |lc| lc + tmp,
                |lc| lc + xl + (self.constants[i], CS::one()),
                |lc| lc + new_xl - xr
            );

            // xR = xL
            xr = xl;
            xr_value = xl_value;

            // xL = new_xL
            xl = new_xl;
            xl_value = new_xl_value;
        }

        Ok(())
    }
}

#[test]
fn test_sonic_mimc() {
    use crate::pairing::ff::{Field, PrimeField};
    use crate::pairing::{Engine, CurveAffine, CurveProjective};
    use crate::pairing::bls12_381::{Bls12, Fr};
    use std::time::{Instant};
    use crate::sonic::srs::SRS;

    let srs_x = Fr::from_str("23923").unwrap();
    let srs_alpha = Fr::from_str("23728792").unwrap();
    println!("making srs");
    let start = Instant::now();
    let srs = SRS::<Bls12>::dummy(830564, srs_x, srs_alpha);
    println!("done in {:?}", start.elapsed());

    {
        // This may not be cryptographically safe, use
        // `OsRng` (for example) in production software.
        let rng = &mut thread_rng();

        // Generate the MiMC round constants
        let constants = (0..MIMC_ROUNDS).map(|_| rng.gen()).collect::<Vec<_>>();
        let samples: usize = 100;

        let xl = rng.gen();
        let xr = rng.gen();
        let image = mimc::<Bls12>(xl, xr, &constants);

        // Create an instance of our circuit (with the
        // witness)
        let circuit = MiMCDemoNoInputs {
            xl: Some(xl),
            xr: Some(xr),
            image: Some(image),
            constants: &constants
        };

        use crate::sonic::sonic::Basic;
        use crate::sonic::sonic::AdaptorCircuit;
        use crate::sonic::helped::prover::{create_advice_on_srs, create_proof_on_srs};
        use crate::sonic::helped::{MultiVerifier, get_circuit_parameters};
        use crate::sonic::helped::helper::{create_aggregate_on_srs};

        println!("creating proof");
        let start = Instant::now();
        let proof = create_proof_on_srs::<Bls12, _, Basic>(&AdaptorCircuit(circuit.clone()), &srs).unwrap();
        println!("done in {:?}", start.elapsed());

        println!("creating advice");
        let start = Instant::now();
        let advice = create_advice_on_srs::<Bls12, _, Basic>(&AdaptorCircuit(circuit.clone()), &proof, &srs).unwrap();
        println!("done in {:?}", start.elapsed());

        println!("creating aggregate for {} proofs", samples);
        let start = Instant::now();
        let proofs: Vec<_> = (0..samples).map(|_| (proof.clone(), advice.clone())).collect();
        let aggregate = create_aggregate_on_srs::<Bls12, _, Basic>(&AdaptorCircuit(circuit.clone()), &proofs, &srs);
        println!("done in {:?}", start.elapsed());

        {
            let rng = thread_rng();
            let mut verifier = MultiVerifier::<Bls12, _, Basic, _>::new(AdaptorCircuit(circuit.clone()), &srs, rng).unwrap();
            println!("verifying 1 proof without advice");
            let start = Instant::now();
            {
                for _ in 0..1 {
                    verifier.add_proof(&proof, &[], |_, _| None);
                }
                assert_eq!(verifier.check_all(), true); // TODO
            }
            println!("done in {:?}", start.elapsed());
        }

        {
            let rng = thread_rng();
            let mut verifier = MultiVerifier::<Bls12, _, Basic, _>::new(AdaptorCircuit(circuit.clone()), &srs, rng).unwrap();
            println!("verifying {} proofs without advice", samples);
            let start = Instant::now();
            {
                for _ in 0..samples {
                    verifier.add_proof(&proof, &[], |_, _| None);
                }
                assert_eq!(verifier.check_all(), true); // TODO
            }
            println!("done in {:?}", start.elapsed());
        }
        
        {
            let rng = thread_rng();
            let mut verifier = MultiVerifier::<Bls12, _, Basic, _>::new(AdaptorCircuit(circuit.clone()), &srs, rng).unwrap();
            println!("verifying 100 proofs with advice");
            let start = Instant::now();
            {
                for (ref proof, ref advice) in &proofs {
                    verifier.add_proof_with_advice(proof, &[], advice);
                }
                verifier.add_aggregate(&proofs, &aggregate);
                assert_eq!(verifier.check_all(), true); // TODO
            }
            println!("done in {:?}", start.elapsed());
        }
    }
}


#[test]
fn test_sonic_mimc_in_permutation_driver() {
    use crate::pairing::ff::{Field, PrimeField};
    use crate::pairing::{Engine, CurveAffine, CurveProjective};
    use crate::pairing::bls12_381::{Bls12, Fr};
    use std::time::{Instant};
    use crate::sonic::srs::SRS;

    let srs_x = Fr::from_str("23923").unwrap();
    let srs_alpha = Fr::from_str("23728792").unwrap();
    println!("making srs");
    let start = Instant::now();
    let srs = SRS::<Bls12>::dummy(830564, srs_x, srs_alpha);
    println!("done in {:?}", start.elapsed());

    {
        // This may not be cryptographically safe, use
        // `OsRng` (for example) in production software.
        let rng = &mut thread_rng();

        // Generate the MiMC round constants
        let constants = (0..MIMC_ROUNDS).map(|_| rng.gen()).collect::<Vec<_>>();
        let samples: usize = 100;

        let xl = rng.gen();
        let xr = rng.gen();
        let image = mimc::<Bls12>(xl, xr, &constants);

        // Create an instance of our circuit (with the
        // witness)
        let circuit = MiMCDemoNoInputs {
            xl: Some(xl),
            xr: Some(xr),
            image: Some(image),
            constants: &constants
        };

        use crate::sonic::sonic::Basic;
        use crate::sonic::sonic::AdaptorCircuit;
        use crate::sonic::helped::prover::{create_advice_on_srs, create_proof_on_srs};
        use crate::sonic::helped::{MultiVerifier, get_circuit_parameters};
        use crate::sonic::helped::helper::{create_aggregate_on_srs};
        use crate::sonic::sonic::Permutation3;

        println!("creating proof");
        let start = Instant::now();
        let proof = create_proof_on_srs::<Bls12, _, Permutation3>(&AdaptorCircuit(circuit.clone()), &srs).unwrap();
        println!("done in {:?}", start.elapsed());

        println!("creating advice");
        let start = Instant::now();
        let advice = create_advice_on_srs::<Bls12, _, Permutation3>(&AdaptorCircuit(circuit.clone()), &proof, &srs).unwrap();
        println!("done in {:?}", start.elapsed());

        println!("creating aggregate for {} proofs", samples);
        let start = Instant::now();
        let proofs: Vec<_> = (0..samples).map(|_| (proof.clone(), advice.clone())).collect();
        let aggregate = create_aggregate_on_srs::<Bls12, _, Permutation3>(&AdaptorCircuit(circuit.clone()), &proofs, &srs);
        println!("done in {:?}", start.elapsed());

        {
            let rng = thread_rng();
            let mut verifier = MultiVerifier::<Bls12, _, Permutation3, _>::new(AdaptorCircuit(circuit.clone()), &srs, rng).unwrap();
            println!("verifying 1 proof without advice");
            let start = Instant::now();
            {
                for _ in 0..1 {
                    verifier.add_proof(&proof, &[], |_, _| None);
                }
                assert_eq!(verifier.check_all(), true); // TODO
            }
            println!("done in {:?}", start.elapsed());
        }

        {
            let rng = thread_rng();
            let mut verifier = MultiVerifier::<Bls12, _, Permutation3, _>::new(AdaptorCircuit(circuit.clone()), &srs, rng).unwrap();
            println!("verifying {} proofs without advice", samples);
            let start = Instant::now();
            {
                for _ in 0..samples {
                    verifier.add_proof(&proof, &[], |_, _| None);
                }
                assert_eq!(verifier.check_all(), true); // TODO
            }
            println!("done in {:?}", start.elapsed());
        }
        
        {
            let rng = thread_rng();
            let mut verifier = MultiVerifier::<Bls12, _, Permutation3, _>::new(AdaptorCircuit(circuit.clone()), &srs, rng).unwrap();
            println!("verifying 100 proofs with advice");
            let start = Instant::now();
            {
                for (ref proof, ref advice) in &proofs {
                    verifier.add_proof_with_advice(proof, &[], advice);
                }
                verifier.add_aggregate(&proofs, &aggregate);
                assert_eq!(verifier.check_all(), true); // TODO
            }
            println!("done in {:?}", start.elapsed());
        }
    }
}

#[test]
fn test_succinct_sonic_mimc() {
    use crate::pairing::ff::{Field, PrimeField};
    use crate::pairing::{Engine, CurveAffine, CurveProjective};
    use crate::pairing::bls12_381::{Bls12, Fr};
    use std::time::{Instant};
    use crate::sonic::srs::SRS;

    let srs_x = Fr::from_str("23923").unwrap();
    let srs_alpha = Fr::from_str("23728792").unwrap();
    println!("making srs");
    let start = Instant::now();
    // let srs = SRS::<Bls12>::dummy(830564, srs_x, srs_alpha);
    let srs = SRS::<Bls12>::dummy(40000000, srs_x, srs_alpha);
    println!("done in {:?}", start.elapsed());

    {
        use rand::{XorShiftRng, SeedableRng, Rand, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        // Generate the MiMC round constants
        // let constants = (0..MIMC_ROUNDS).map(|_| rng.gen()).collect::<Vec<_>>();
        let constants = (0..MIMC_ROUNDS).map(|_| Fr::one()).collect::<Vec<_>>();
        let samples: usize = 100;

        let xl = rng.gen();
        let xr = rng.gen();
        let image = mimc::<Bls12>(xl, xr, &constants);

        // Create an instance of our circuit (with the
        // witness)
        let circuit = MiMCDemoNoInputs::<Bls12> {
            xl: Some(xl),
            xr: Some(xr),
            image: Some(image),
            constants: &constants
        };

        use crate::sonic::sonic::Basic;
        use crate::sonic::sonic::AdaptorCircuit;
        use crate::sonic::helped::prover::{create_advice_on_srs, create_proof_on_srs};
        use crate::sonic::helped::{get_circuit_parameters_for_succinct_sonic, MultiVerifier};
        use crate::sonic::sonic::Permutation3;
        use crate::sonic::unhelped::permutation_structure::*;
        use crate::sonic::unhelped::SuccinctMultiVerifier;
        use crate::sonic::unhelped::{create_aggregate_on_srs};

        use crate::sonic::cs::{Circuit, ConstraintSystem, LinearCombination, Coeff};

        let perm_structure = create_permutation_structure::<Bls12, _>(&AdaptorCircuit(circuit.clone()));
        let s1_srs = perm_structure.create_permutation_special_reference(&srs);
        // let s2_srs = perm_structure.calculate_s2_commitment_value(&srs);

        let info = get_circuit_parameters_for_succinct_sonic::<Bls12, _>(circuit.clone()).expect("Must get circuit info");
        println!("{:?}", info);

        println!("creating proof");
        let start = Instant::now();
        let proof = create_proof_on_srs::<Bls12, _, Permutation3>(&AdaptorCircuit(circuit.clone()), &srs).unwrap();
        println!("done in {:?}", start.elapsed());

        println!("creating advice");
        let start = Instant::now();
        let advice = create_advice_on_srs::<Bls12, _, Permutation3>(&AdaptorCircuit(circuit.clone()), &proof, &srs).unwrap();
        println!("done in {:?}", start.elapsed());

        println!("creating aggregate for {} proofs", samples);
        let start = Instant::now();
        let proofs: Vec<_> = (0..samples).map(|_| (proof.clone(), advice.clone())).collect();
        let aggregate = create_aggregate_on_srs::<Bls12, _, Permutation3>(&AdaptorCircuit(circuit.clone()), &proofs, &srs, &s1_srs);
        println!("done in {:?}", start.elapsed());

        // {
        //     let rng = thread_rng();
        //     let mut verifier = MultiVerifier::<Bls12, _, Permutation3, _>::new(AdaptorCircuit(circuit.clone()), &srs, rng).unwrap();
        //     println!("verifying 1 proof without advice");
        //     let start = Instant::now();
        //     {
        //         for _ in 0..1 {
        //             verifier.add_proof(&proof, &[], |_, _| None);
        //         }
        //         assert_eq!(verifier.check_all(), true); // TODO
        //     }
        //     println!("done in {:?}", start.elapsed());
        // }

        // {
        //     let rng = thread_rng();
        //     let mut verifier = MultiVerifier::<Bls12, _, Permutation3, _>::new(AdaptorCircuit(circuit.clone()), &srs, rng).unwrap();
        //     println!("verifying {} proofs without advice", samples);
        //     let start = Instant::now();
        //     {
        //         for _ in 0..samples {
        //             verifier.add_proof(&proof, &[], |_, _| None);
        //         }
        //         assert_eq!(verifier.check_all(), true); // TODO
        //     }
        //     println!("done in {:?}", start.elapsed());
        // }

        {
            use rand::{XorShiftRng, SeedableRng, Rand, Rng};
            let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

            let mut verifier = SuccinctMultiVerifier::<Bls12, _, Permutation3, _>::new(AdaptorCircuit(circuit.clone()), &srs, rng).unwrap();
            println!("verifying 100 proofs with succinct advice");
            let start = Instant::now();
            {
                for (ref proof, ref advice) in &proofs {
                    verifier.add_proof_with_advice(proof, &[], advice);
                }
                verifier.add_aggregate(
                    &proofs,
                    &aggregate,
                    &srs,
                );
                assert_eq!(verifier.check_all(), true); // TODO
            }
            println!("done in {:?}", start.elapsed());
        }
    }
}

#[test]
fn test_inputs_into_sonic_mimc() {
    use crate::pairing::ff::{Field, PrimeField};
    use crate::pairing::{Engine, CurveAffine, CurveProjective};
    use crate::pairing::bn256::{Bn256, Fr};
    // use crate::pairing::bls12_381::{Bls12, Fr};
    use std::time::{Instant};
    use crate::sonic::srs::SRS;

    let srs_x = Fr::from_str("23923").unwrap();
    let srs_alpha = Fr::from_str("23728792").unwrap();
    println!("making srs");
    let start = Instant::now();
    let srs = SRS::<Bn256>::dummy(830564, srs_x, srs_alpha);
    println!("done in {:?}", start.elapsed());

    {
        // This may not be cryptographically safe, use
        // `OsRng` (for example) in production software.
        let rng = &mut thread_rng();

        // Generate the MiMC round constants
        let constants = (0..MIMC_ROUNDS).map(|_| rng.gen()).collect::<Vec<_>>();
        let samples: usize = 100;

        let xl = rng.gen();
        let xr = rng.gen();
        let image = mimc::<Bn256>(xl, xr, &constants);

        // Create an instance of our circuit (with the
        // witness)
        let circuit = MiMCDemo {
            xl: Some(xl),
            xr: Some(xr),
            constants: &constants
        };

        use crate::sonic::sonic::Basic;
        use crate::sonic::sonic::AdaptorCircuit;
        use crate::sonic::helped::prover::{create_advice_on_srs, create_proof_on_srs};
        use crate::sonic::helped::{MultiVerifier, get_circuit_parameters};
        use crate::sonic::helped::helper::{create_aggregate_on_srs};

        let info = get_circuit_parameters::<Bn256, _>(circuit.clone()).expect("Must get circuit info");
        println!("{:?}", info);

        println!("creating proof");
        let start = Instant::now();
        let proof = create_proof_on_srs::<Bn256, _, Basic>(&AdaptorCircuit(circuit.clone()), &srs).unwrap();
        println!("done in {:?}", start.elapsed());

        println!("creating advice");
        let start = Instant::now();
        let advice = create_advice_on_srs::<Bn256, _, Basic>(&AdaptorCircuit(circuit.clone()), &proof, &srs).unwrap();
        println!("done in {:?}", start.elapsed());

        println!("creating aggregate for {} proofs", samples);
        let start = Instant::now();
        let proofs: Vec<_> = (0..samples).map(|_| (proof.clone(), advice.clone())).collect();
        let aggregate = create_aggregate_on_srs::<Bn256, _, Basic>(&AdaptorCircuit(circuit.clone()), &proofs, &srs);
        println!("done in {:?}", start.elapsed());

        {
            let rng = thread_rng();
            let mut verifier = MultiVerifier::<Bn256, _, Basic, _>::new(AdaptorCircuit(circuit.clone()), &srs, rng).unwrap();
            println!("verifying 1 proof without advice");
            let start = Instant::now();
            {
                for _ in 0..1 {
                    verifier.add_proof(&proof, &[image], |_, _| None);
                }
                assert_eq!(verifier.check_all(), true); // TODO
            }
            println!("done in {:?}", start.elapsed());
        }

        {
            let rng = thread_rng();
            let mut verifier = MultiVerifier::<Bn256, _, Basic, _>::new(AdaptorCircuit(circuit.clone()), &srs, rng).unwrap();
            println!("verifying {} proofs without advice", samples);
            let start = Instant::now();
            {
                for _ in 0..samples {
                    verifier.add_proof(&proof, &[image], |_, _| None);
                }
                assert_eq!(verifier.check_all(), true); // TODO
            }
            println!("done in {:?}", start.elapsed());
        }
        
        {
            let rng = thread_rng();
            let mut verifier = MultiVerifier::<Bn256, _, Basic, _>::new(AdaptorCircuit(circuit.clone()), &srs, rng).unwrap();
            println!("verifying 100 proofs with advice and aggregate");
            let start = Instant::now();
            {
                for (ref proof, ref advice) in &proofs {
                    verifier.add_proof_with_advice(proof, &[image], advice);
                }
                verifier.add_aggregate(&proofs, &aggregate);
                assert_eq!(verifier.check_all(), true); // TODO
            }
            println!("done in {:?}", start.elapsed());
        }
    }
}

#[test]
fn test_high_level_sonic_api() {
    use crate::pairing::bn256::{Bn256};
    use std::time::{Instant};
    use crate::sonic::helped::{
        generate_random_parameters, 
        verify_aggregate, 
        verify_proofs, 
        create_proof, 
        create_advice,
        create_aggregate,
        get_circuit_parameters
    };

    {
        // This may not be cryptographically safe, use
        // `OsRng` (for example) in production software.
        let mut rng = &mut thread_rng();

        // Generate the MiMC round constants
        let constants = (0..MIMC_ROUNDS).map(|_| rng.gen()).collect::<Vec<_>>();
        let samples: usize = 100;

        let xl = rng.gen();
        let xr = rng.gen();
        let image = mimc::<Bn256>(xl, xr, &constants);

        // Create an instance of our circuit (with the
        // witness)
        let circuit = MiMCDemo {
            xl: Some(xl),
            xr: Some(xr),
            constants: &constants
        };

        let info = get_circuit_parameters::<Bn256, _>(circuit.clone()).expect("Must get circuit info");
        println!("{:?}", info);

        let params = generate_random_parameters(circuit.clone(), &mut rng).unwrap();

        println!("creating proof");
        let start = Instant::now();
        let proof = create_proof(circuit.clone(), &params).unwrap();
        println!("done in {:?}", start.elapsed());

        println!("creating advice");
        let start = Instant::now();
        let advice = create_advice(circuit.clone(), &proof, &params).unwrap();
        println!("done in {:?}", start.elapsed());

        println!("creating aggregate for {} proofs", samples);
        let proofs: Vec<_> = (0..samples).map(|_| (proof.clone(), advice.clone())).collect();

        let start = Instant::now();
        let aggregate = create_aggregate::<Bn256, _>(circuit.clone(), &proofs, &params);
        println!("done in {:?}", start.elapsed());

        {
            println!("verifying 1 proof without advice");
            let rng = thread_rng();
            let start = Instant::now();
            assert_eq!(verify_proofs(&vec![proof.clone()], &vec![vec![image.clone()]], circuit.clone(), rng, &params).unwrap(), true);
            println!("done in {:?}", start.elapsed());
        }

        {
            println!("verifying {} proofs without advice", samples);
            let rng = thread_rng();
            let start = Instant::now();
            assert_eq!(verify_proofs(&vec![proof.clone(); 100], &vec![vec![image.clone()]; 100], circuit.clone(), rng, &params).unwrap(), true);
            println!("done in {:?}", start.elapsed());
        }
        
        {
            println!("verifying 100 proofs with advice and aggregate");
            let rng = thread_rng();
            let start = Instant::now();
            assert_eq!(verify_aggregate(&vec![(proof.clone(), advice.clone()); 100], &aggregate, &vec![vec![image.clone()]; 100], circuit.clone(), rng, &params).unwrap(), true);
            println!("done in {:?}", start.elapsed());
        }
    }
}

// #[test]
// fn test_constraints_info() {
//     use crate::pairing::bn256::{Bn256};
//     use std::time::{Instant};
//     use crate::sonic::unhelped::padding::{constraints_info};
//     {
//         // This may not be cryptographically safe, use
//         // `OsRng` (for example) in production software.
//         let mut rng = &mut thread_rng();

//         // Generate the MiMC round constants
//         let constants = (0..MIMC_ROUNDS).map(|_| rng.gen()).collect::<Vec<_>>();

//         let xl = rng.gen();
//         let xr = rng.gen();
//         let image = mimc::<Bn256>(xl, xr, &constants);

//         // Create an instance of our circuit (with the
//         // witness)
//         let circuit = MiMCDemo {
//             xl: Some(xl),
//             xr: Some(xr),
//             constants: &constants
//         };

//         constraints_info::<Bn256, _>(circuit.clone());
//     }
// }

// #[test]
// fn test_padding_using_mimc() {
//     use crate::pairing::ff::{Field, PrimeField};
//     use crate::pairing::{Engine, CurveAffine, CurveProjective};
//     use crate::pairing::bls12_381::{Bls12, Fr};
//     use std::time::{Instant};
//     use crate::sonic::srs::SRS;

//     let srs_x = Fr::from_str("23923").unwrap();
//     let srs_alpha = Fr::from_str("23728792").unwrap();
//     println!("making srs");
//     let start = Instant::now();
//     let srs = SRS::<Bls12>::dummy(830564, srs_x, srs_alpha);
//     println!("done in {:?}", start.elapsed());

//     {
//         // This may not be cryptographically safe, use
//         // `OsRng` (for example) in production software.
//         let rng = &mut thread_rng();

//         // Generate the MiMC round constants
//         let constants = (0..MIMC_ROUNDS).map(|_| rng.gen()).collect::<Vec<_>>();
//         let samples: usize = 100;

//         let xl = rng.gen();
//         let xr = rng.gen();
//         let image = mimc::<Bls12>(xl, xr, &constants);

//         // Create an instance of our circuit (with the
//         // witness)
//         let circuit = MiMCDemoNoInputs {
//             xl: Some(xl),
//             xr: Some(xr),
//             image: Some(image),
//             constants: &constants
//         };

//         use crate::sonic::cs::Basic;
//         use crate::sonic::sonic::AdaptorCircuit;
//         use crate::sonic::helped::prover::{create_advice_on_srs, create_proof_on_srs};
//         use crate::sonic::helped::{MultiVerifier, get_circuit_parameters};
//         use crate::sonic::helped::helper::{create_aggregate_on_srs};
//         use crate::sonic::unhelped::padding::Padding;

//         let info = get_circuit_parameters::<Bls12, _>(circuit.clone()).expect("Must get circuit info");
//         println!("{:?}", info);

//         println!("creating proof");
//         let start = Instant::now();
//         let proof = create_proof_on_srs::<Bls12, _, Padding>(&AdaptorCircuit(circuit.clone()), &srs).unwrap();
//         println!("done in {:?}", start.elapsed());

//         {
//             let rng = thread_rng();
//             let mut verifier = MultiVerifier::<Bls12, _, Padding, _>::new(AdaptorCircuit(circuit.clone()), &srs, rng).unwrap();
//             println!("K map = {:?}", verifier.get_k_map());
//             println!("verifying 1 proof without advice");
//             let start = Instant::now();
//             {
//                 for _ in 0..1 {
//                     verifier.add_proof(&proof, &[], |_, _| None);
//                 }
//                 assert_eq!(verifier.check_all(), true); // TODO
//             }
//             println!("done in {:?}", start.elapsed());
//         }
//     }
// }