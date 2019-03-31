
#[test]
fn test_paper_results() {
    use crate::pairing::bls12_381::{Bls12, Fr};
    use std::time::{Instant};

    let srs_x = Fr::from_str("23923").unwrap();
    let srs_alpha = Fr::from_str("23728792").unwrap();
    println!("making srs");
    let start = Instant::now();
    let srs = SRS::<Bls12>::dummy(830564, srs_x, srs_alpha);
    println!("done in {:?}", start.elapsed());

    struct PedersenHashPreimageCircuit<'a, E: sapling_crypto::jubjub::JubjubEngine + 'a> {
        preimage: Vec<Option<bool>>,
        params: &'a E::Params,
    }

    impl<'a, E: sapling_crypto::jubjub::JubjubEngine + 'a> Clone for PedersenHashPreimageCircuit<'a, E> {
        fn clone(&self) -> Self {
            PedersenHashPreimageCircuit {
                preimage: self.preimage.clone(),
                params: self.params
            }
        }
    }

    impl<'a, E: sapling_crypto::jubjub::JubjubEngine> bellman::Circuit<E> for PedersenHashPreimageCircuit<'a, E> {
        fn synthesize<CS: bellman::ConstraintSystem<E>>(
            self,
            cs: &mut CS
        ) -> Result<(), bellman::SynthesisError>
        {
            //use bellman::ConstraintSystem;
            use sapling_crypto::circuit::boolean::{AllocatedBit, Boolean};
            use sapling_crypto::circuit::pedersen_hash;

            let mut preimage = vec![];

            for &bit in self.preimage.iter() {
                preimage.push(Boolean::from(AllocatedBit::alloc(&mut* cs, bit)?));
            }

            pedersen_hash::pedersen_hash(
                &mut* cs, pedersen_hash::Personalization::NoteCommitment, &preimage, self.params)?;

            Ok(())
        }
    }

    #[derive(Clone)]
    struct SHA256PreimageCircuit {
        preimage: Vec<Option<bool>>,
    }

    impl<E: Engine> bellman::Circuit<E> for SHA256PreimageCircuit {
        fn synthesize<CS: bellman::ConstraintSystem<E>>(
            self,
            cs: &mut CS,
        ) -> Result<(), bellman::SynthesisError> {
            //use bellman::ConstraintSystem;
            use sapling_crypto::circuit::boolean::{AllocatedBit, Boolean};
            use sapling_crypto::circuit::sha256::sha256_block_no_padding;

            let mut preimage = vec![];

            for &bit in self.preimage.iter() {
                preimage.push(Boolean::from(AllocatedBit::alloc(&mut *cs, bit)?));
            }

            sha256_block_no_padding(&mut *cs, &preimage)?;
            sha256_block_no_padding(&mut *cs, &preimage)?;
            sha256_block_no_padding(&mut *cs, &preimage)?;
            // sha256_block_no_padding(&mut *cs, &preimage)?;

            Ok(())
        }
    }

    {
        use crate::pairing::{CurveAffine};
        use crate::pairing::bls12_381::{G1Affine, G2Affine};
        let a = G1Affine::one();
        let b = G2Affine::one();
        let c = G1Affine::one();

        let alpha = G1Affine::one();
        let beta = G2Affine::one();
        let iv = G1Affine::one();
        let gamma = G2Affine::one().prepare();
        let delta = G2Affine::one().prepare();

        let alphabeta = <Bls12 as Engine>::pairing(alpha, beta);

        println!("verifying an idealized groth16 proof");
        let start = Instant::now();
        assert!(<Bls12 as Engine>::final_exponentiation(
            &<Bls12 as Engine>::miller_loop([
                (&a.prepare(), &b.prepare()),
                (&iv.prepare(), &gamma),
                (&c.prepare(), &delta),
            ].into_iter())
        ).unwrap() != alphabeta);
        println!("done in {:?}", start.elapsed());
    }

    {
        use sonic::util::multiexp;
        use crate::pairing::{CurveAffine};
        use crate::pairing::bls12_381::{G1Affine, G2Affine};
        // e([\alpha G], [\beta H]) = e(A, B) e(IV, [\gamma] H) e(C, [\delta] H)
        let a = G1Affine::one();
        let b = G2Affine::one();
        let c = vec![G1Affine::one(); 100];
        let mut tmp = Fr::one();
        tmp.double();
        tmp = tmp.inverse().unwrap();
        let cscalars = (0..100).map(|_| {tmp.square(); tmp}).collect::<Vec<_>>();

        let alpha = G1Affine::one();
        let beta = G2Affine::one();
        let iv = G1Affine::one();
        let gamma = G2Affine::one().prepare();
        let delta = G2Affine::one().prepare();

        let alphabeta = <Bls12 as Engine>::pairing(alpha, beta);

        println!("verifying 100 idealized groth16 proofs");
        let start = Instant::now();
        let c = multiexp(
            c.iter(),
            cscalars.iter(),
        ).into_affine();
        assert!(<Bls12 as Engine>::final_exponentiation(
            &<Bls12 as Engine>::miller_loop([
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&iv.prepare(), &gamma),
                (&c.prepare(), &delta),
            ].into_iter())
        ).unwrap() != alphabeta);
        println!("done in {:?}", start.elapsed());
    }

    {
        let samples: usize = 100;

        const NUM_BITS: usize = 384;

        let params = sapling_crypto::jubjub::JubjubBls12::new();
        let circuit = PedersenHashPreimageCircuit {
            preimage: vec![Some(true); NUM_BITS],
            params: &params
        };

        println!("creating proof");
        let start = Instant::now();
        let proof = create_proof::<Bls12, _, Basic>(&AdaptorCircuit(circuit.clone()), &srs).unwrap();
        println!("done in {:?}", start.elapsed());

        println!("creating advice");
        let start = Instant::now();
        let advice = create_advice::<Bls12, _, Basic>(&AdaptorCircuit(circuit.clone()), &proof, &srs);
        println!("done in {:?}", start.elapsed());

        println!("creating aggregate for {} proofs", samples);
        let start = Instant::now();
        let proofs: Vec<_> = (0..samples).map(|_| (proof.clone(), advice.clone())).collect();
        let aggregate = create_aggregate::<Bls12, _, Basic>(&AdaptorCircuit(circuit.clone()), &proofs, &srs);
        println!("done in {:?}", start.elapsed());

        {
            let mut verifier = MultiVerifier::<Bls12, _, Basic>::new(AdaptorCircuit(circuit.clone()), &srs).unwrap();
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
            let mut verifier = MultiVerifier::<Bls12, _, Basic>::new(AdaptorCircuit(circuit.clone()), &srs).unwrap();
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
            let mut verifier = MultiVerifier::<Bls12, _, Basic>::new(AdaptorCircuit(circuit.clone()), &srs).unwrap();
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
