use crate::pairing::ff::{Field};
use crate::pairing::{Engine, CurveProjective};
use std::marker::PhantomData;
use rand::{Rand, Rng};

use crate::sonic::helped::{Proof, SxyAdvice};
use crate::sonic::helped::batch::Batch;
use crate::sonic::helped::poly::{SxEval, SyEval};
use crate::sonic::helped::helper::Aggregate;
use crate::sonic::helped::parameters::{Parameters};

use crate::SynthesisError;

use crate::sonic::transcript::{Transcript, TranscriptProtocol};
use crate::sonic::util::*;
use crate::sonic::cs::{Backend, SynthesisDriver};
use crate::sonic::cs::{Circuit, Variable, Coeff};
use crate::sonic::srs::SRS;
use crate::sonic::sonic::Preprocess;

use super::s2_proof::{S2Proof, S2Eval};
use super::aggregate::SuccinctAggregate;
use super::permutation_structure::create_permutation_structure;
use super::permutation_argument::{
    PermutationArgumentProof, 
    PermutationProof, 
    PermutationArgument,
    SpecializedSRS
};

pub struct SuccinctMultiVerifier<E: Engine, C: Circuit<E>, S: SynthesisDriver, R: Rng> {
    circuit: C,
    s1_special_reference: SpecializedSRS<E>,
    s2_special_reference: E::G1Affine,
    pub(crate) batch: Batch<E>,
    k_map: Vec<usize>,
    n: usize,
    q: usize,
    randomness_source: R,
    _marker: PhantomData<(E, S)>
}

impl<E: Engine, C: Circuit<E>, S: SynthesisDriver, R: Rng> SuccinctMultiVerifier<E, C, S, R> {
    // This constructor consumes randomness source cause it's later used internally
    pub fn new(circuit: C, srs: &SRS<E>, rng: R) -> Result<Self, SynthesisError> {
        let (n, q, k_map) = {
            let mut preprocess = Preprocess::new();
            S::synthesize(&mut preprocess, &circuit)?;

            (preprocess.n, preprocess.q, preprocess.k_map)
        };

        // also calculate special reference for s1

        let permutation_structure = create_permutation_structure(&circuit);
        let s2_special_reference = permutation_structure.calculate_s2_commitment_value(&srs);
        let s1_special_reference = permutation_structure.create_permutation_special_reference(&srs);

        Ok(SuccinctMultiVerifier {
            circuit,
            s1_special_reference,
            s2_special_reference,
            batch: Batch::new(srs, n),
            k_map: k_map,
            n: n,
            q: q,
            randomness_source: rng,
            _marker: PhantomData
        })
    }

    pub fn add_aggregate(
        &mut self,
        proofs: &[(Proof<E>, SxyAdvice<E>)],
        aggregate: &SuccinctAggregate<E>,
        srs: &SRS<E>
    )
    {
        let mut transcript = Transcript::new(&[]);
        let mut y_values: Vec<E::Fr> = Vec::with_capacity(proofs.len());
        for &(ref proof, ref sxyadvice) in proofs {
            {
                let mut transcript = Transcript::new(&[]);
                transcript.commit_point(&proof.r);
                y_values.push(transcript.get_challenge_scalar());
            }

            transcript.commit_point(&sxyadvice.s);
        }

        let z: E::Fr = transcript.get_challenge_scalar();

        transcript.commit_point(&aggregate.c);

        let w: E::Fr = transcript.get_challenge_scalar();

        let szw = {
            // prover will supply s1 and s2, need to calculate 
            // s(z, w) = X^-(N+1) * Y^N * s1 - X^N * s2

            let x_n = z.pow(&[self.n as u64]);
            let mut x_n_plus_1 = x_n;
            x_n_plus_1.mul_assign(&z);
            let x_n_plus_1_inv = x_n_plus_1.inverse().unwrap();

            let y_n = w.pow(&[self.n as u64]);

            // simultaneously add components to the batch verifier

            // this is s2 contribution itself
            let s2_proof = &aggregate.s2_proof;
            let mut s2_part = s2_proof.c_value;
            s2_part.add_assign(&s2_proof.d_value);
            s2_part.mul_assign(&x_n);

            // add terms for S2 for verification

            {
                let random: E::Fr = self.randomness_source.gen();

                // e(C,hαx)e(C−yz,hα) = e(O,h)e(g−c,hα) that is 
                // e(C,hαx)e(C^−yz,hα)*e(O,-h)e(g^c,hα) = 1

                let mut xy = z;
                xy.mul_assign(&w);

                self.batch.add_opening(s2_proof.c_opening, random, xy);
                self.batch.add_opening_value(random, s2_proof.c_value);
                self.batch.add_commitment(self.s2_special_reference, random);

            }

            {
                let random: E::Fr = self.randomness_source.gen();

                // e(D,hαx)e(D−y−1z,hα) = e(O,h)e(g−d,hα) that is 
                // e(D,hαx)e(D^−y-1z,hα)*e(O,-h)e(g^d,hα) = 1

                let mut y_inv_by_x = z;
                y_inv_by_x.mul_assign(&w.inverse().unwrap());

                self.batch.add_opening(s2_proof.d_opening, random, y_inv_by_x);
                self.batch.add_opening_value(random, s2_proof.d_value);
                self.batch.add_commitment(self.s2_special_reference, random);

            }

            // now work with s1 part

            let mut s1_part = aggregate.signature.perm_argument_proof.s_zy;
            s1_part.mul_assign(&x_n_plus_1_inv);
            s1_part.mul_assign(&y_n);

            let mut szw = s1_part;
            szw.sub_assign(&s2_part);

            // verify commitments for s' and s

            {
                let mut transcript = Transcript::new(&[]);

                // let s_commitments = &aggregate.signature.s_commitments;
                // let s_prime_commitments = &aggregate.signature.s_prime_commitments;

                let mut challenges = vec![];
                for (s, s_prime) in aggregate.signature.s_commitments.iter()
                                    .zip(aggregate.signature.s_prime_commitments.iter()) {
                    transcript.commit_point(s);
                    transcript.commit_point(s_prime);
                }     

                for _ in 0..aggregate.signature.s_commitments.len() {
                    let challenge = transcript.get_challenge_scalar();
                        challenges.push(challenge);
                }

                let z_prime: E::Fr = transcript.get_challenge_scalar();

                // we expect M permutation proofs, add them all into verification
                // using batching with random challenges and extra randomness for pairing equation
                {
                    // e(E,hαx)e(E−z′,hα) = e(􏰇Mj=1Sj′rj,h)e(g−v,hα)
                    let perm_proof = &aggregate.signature.perm_proof;

                    let s_r = multiexp(
                        aggregate.signature.s_prime_commitments.iter(), 
                        challenges.iter()
                    ).into_affine();

                    let p2_r = multiexp(
                        self.s1_special_reference.p_2.iter(),
                        challenges.iter()
                    ).into_affine();


                    let value = perm_proof.v_zy;

                    let random: E::Fr = self.randomness_source.gen();

                    self.batch.add_opening(perm_proof.e_opening, random, z_prime);
                    self.batch.add_opening_value(random, value);
                    self.batch.add_commitment(s_r, random);


                    // e(F,hαx)e(F−yz′,hα) = e(􏰇Mj=1P2jrj,h)e(g−v,hα)

                    let mut y_z_prime = z_prime;
                    y_z_prime.mul_assign(&w);

                    let random: E::Fr = self.randomness_source.gen();

                    self.batch.add_opening(perm_proof.f_opening, random, y_z_prime);
                    self.batch.add_opening_value(random, value);
                    self.batch.add_commitment(p2_r, random);

                }

                // now we can actually take an opening of S commitments and 

                {
                    // e(I,hαx)e(I−z,hα) = e(􏰇Mj=1 Sj,h)e(g−s,hα)

                    let value = aggregate.signature.perm_argument_proof.s_zy;
                    let mut s_commitment = E::G1::zero();

                    for s in aggregate.signature.s_commitments.iter() {
                        s_commitment.add_assign_mixed(s);
                    }

                    let random: E::Fr = self.randomness_source.gen();

                    self.batch.add_opening(aggregate.signature.perm_argument_proof.s_opening, random, z);
                    self.batch.add_opening_value(random, value);
                    self.batch.add_commitment(s_commitment.into_affine(), random);

                }

                // TODO: Add grand product argument!

                // for each of the grand product arguments create a corresponding commitment
                // from already known elements

                let mut betas = vec![];
                let mut gammas = vec![];

                let mut a_commitments = vec![];
                let mut b_commitments = vec![];

                for _ in 0..aggregate.signature.s_commitments.len() {
                    let beta: E::Fr = transcript.get_challenge_scalar();
                    let gamma: E::Fr = transcript.get_challenge_scalar();

                    betas.push(beta);
                    gammas.push(gamma);
                }
                
                let mut wellformedness_argument_commitments = vec![];

                use crate::pairing::CurveAffine;
                use crate::pairing::ff::PrimeField;

                for (j, (((s, s_prime), beta), gamma)) in aggregate.signature.s_commitments.iter()
                                                .zip(aggregate.signature.s_prime_commitments.iter())
                                                .zip(betas.iter())
                                                .zip(gammas.iter())
                                                .enumerate()

                {
                    // Sj(P4j)β(P1j)γ

                    let mut a = s.into_projective();
                    a.add_assign(&self.s1_special_reference.p_4[j].mul(beta.into_repr()));
                    a.add_assign(&self.s1_special_reference.p_1.mul(gamma.into_repr()));
                    let a = a.into_affine();

                    // Sj′(P3j)β(P1j)γ

                    let mut b = s_prime.into_projective();
                    b.add_assign(&self.s1_special_reference.p_3.mul(beta.into_repr()));
                    b.add_assign(&self.s1_special_reference.p_1.mul(gamma.into_repr()));
                    let b = b.into_affine();

                    a_commitments.push(a);
                    b_commitments.push(b);
                    wellformedness_argument_commitments.push(a);
                    wellformedness_argument_commitments.push(b);
                }

                // commitments to invidvidual grand products are assembled, now check first part of a grand
                // product argument

                // Now perform an actual check
                {
                    let randomness: Vec<E::Fr> = (0..aggregate.signature.s_commitments.len()).map(|_| self.randomness_source.gen()).collect();
                    // e(Dj,hαx)e(D−yz,hα) = e(Aj,h)e(Bj,hxn+1)e(g−aj ,hα)

                    let g = srs.g_positive_x[0];
                    let h_alpha_x_precomp = srs.h_positive_x_alpha[1].prepare();
                    let h_alpha_precomp = srs.h_positive_x_alpha[0].prepare();

                    let mut h_x_n_plus_one_precomp = srs.h_positive_x[self.n+1];
                    h_x_n_plus_one_precomp.negate();
                    let h_x_n_plus_one_precomp = h_x_n_plus_one_precomp.prepare();

                    let mut h_prep = srs.h_positive_x[0];
                    h_prep.negate();
                    let h_prep = h_prep.prepare();

                    let a = multiexp(
                        a_commitments.iter(),
                        randomness.iter(),
                    ).into_affine();

                    let a = a.prepare();

                    let b = multiexp(
                        b_commitments.iter(),
                        randomness.iter(),
                    ).into_affine();

                    let b = b.prepare();

                    let mut yz_neg = w;
                    yz_neg.mul_assign(&z);
                    yz_neg.negate();

                    let mut ops = vec![];
                    let mut value = E::Fr::zero();

                    for (el, r) in aggregate.signature.grand_product_signature.grand_product_openings.iter().zip(randomness.iter()) {
                        let (v, o) = el;
                        ops.push(o.clone());
                        let mut val = *v;
                        val.mul_assign(&r);
                        value.add_assign(&val);
                    }

                    let value = g.mul(value.into_repr()).into_affine().prepare();

                    let openings = multiexp(
                        ops.iter(),
                        randomness.iter(),
                    ).into_affine();

                    let openings_zy = openings.mul(yz_neg.into_repr()).into_affine().prepare();
                    let openings = openings.prepare();

                    // e(Dj,hαx)e(D−yz,hα) = e(Aj,h)e(Bj,hxn+1)e(g−aj ,hα)

                    let valid = E::final_exponentiation(&E::miller_loop(&[
                            (&openings, &h_alpha_x_precomp),
                            (&openings_zy, &h_alpha_precomp),
                            (&a, &h_prep),
                            (&b, &h_x_n_plus_one_precomp),
                            (&value, &h_alpha_precomp)
                        ])).unwrap() == E::Fqk::one();

                    // TODO
                    assert!(valid, "grand product arguments must be valid for individual commitments");

                }

                // Now the second part of the grand product argument

                {
                    let mut grand_product_challenges = vec![];

                    for _ in 0..aggregate.signature.grand_product_signature.c_commitments.len() {
                        let c: E::Fr = transcript.get_challenge_scalar();
                        grand_product_challenges.push(c);
                    }
                    // first re-calculate cj and t(z,y)

                    let mut yz = w;
                    yz.mul_assign(&z);

                    let z_inv = z.inverse().unwrap();

                    let mut t_zy = E::Fr::zero();

                    let mut commitments_points = vec![];
                    let mut rc_vec = vec![];
                    let mut ry_vec = vec![];

                    // in grand product arguments n is not a number of gates, but 3n+1 - number of variables + 1
                    let three_n_plus_1 = 3*self.n + 1;

                    for ((r, commitment), (a, _)) in grand_product_challenges.iter()
                                                    .zip(aggregate.signature.grand_product_signature.c_commitments.iter())
                                                    .zip(aggregate.signature.grand_product_signature.grand_product_openings.iter())
                    {
                        let (c, v) = commitment;
                        commitments_points.push(*c);
                        
                        // cj = ((aj + vj(yz)n+1)y + zn+2 + zn+1y − z2n+2y)z−1
                        let mut c_zy = yz.pow([(three_n_plus_1 + 1) as u64]);
                        c_zy.mul_assign(v);
                        c_zy.add_assign(a);
                        c_zy.mul_assign(&w);

                        let mut z_n_plus_1 = z.pow([(three_n_plus_1 + 1) as u64]);

                        let mut z_n_plus_2 = z_n_plus_1;
                        z_n_plus_2.mul_assign(&z);

                        let mut z_2n_plus_2 = z_n_plus_1;
                        z_2n_plus_2.square();
                        z_2n_plus_2.mul_assign(&w);

                        z_n_plus_1.mul_assign(&w);

                        c_zy.add_assign(&z_n_plus_1);
                        c_zy.add_assign(&z_n_plus_2);
                        c_zy.sub_assign(&z_2n_plus_2);

                        c_zy.mul_assign(&z_inv);

                        let mut rc = c_zy;
                        rc.mul_assign(&r);
                        rc_vec.push(rc);

                        let mut ry = w;
                        ry.mul_assign(&r);
                        ry_vec.push(ry);

                        let mut val = rc;
                        val.sub_assign(&r);
                        t_zy.add_assign(&val);
                    }

                    t_zy.add_assign(&aggregate.signature.grand_product_signature.proof.e_zinv);
                    t_zy.sub_assign(&aggregate.signature.grand_product_signature.proof.f_y);

                    // t(z, y) is now calculated

                    let c_rc = multiexp(
                        commitments_points.iter(),
                        rc_vec.iter(),
                    ).into_affine();

                    let c_ry = multiexp(
                        commitments_points.iter(),
                        ry_vec.iter(),
                    ).into_affine();

                    // e(E,h^alphax)e(E^-z^-1,h^alpha) = e(\sumCj^(rj*cj),h)e(g^-e,h^alpha)

                    {
                        let random: E::Fr = self.randomness_source.gen();

                        self.batch.add_opening(aggregate.signature.grand_product_signature.proof.e_opening, random, z_inv);
                        self.batch.add_opening_value(random, aggregate.signature.grand_product_signature.proof.e_zinv);
                        self.batch.add_commitment(c_rc, random);
                    }

                    // e(F,h^alphax)e(F^-y,h) = e(\sumCj^(rj&y),h)e(g^-f,h^alpha)

                    {
                        let random: E::Fr = self.randomness_source.gen();

                        self.batch.add_opening(aggregate.signature.grand_product_signature.proof.f_opening, random, w);
                        self.batch.add_opening_value(random, aggregate.signature.grand_product_signature.proof.f_y);
                        self.batch.add_commitment(c_ry, random);
                    }

                    // e(T′,hαx)e(T′−z,hα) = e(T,h)e(g−t(z,y),hα)

                    {
                        let random: E::Fr = self.randomness_source.gen();

                        self.batch.add_opening(aggregate.signature.grand_product_signature.proof.t_opening, random, z);
                        self.batch.add_opening_value(random, t_zy);
                        self.batch.add_commitment(aggregate.signature.grand_product_signature.t_commitment, random);
                    }
                }

                // finally check the wellformedness arguments

                {
                    let mut wellformedness_challenges = vec![];

                    for _ in 0..wellformedness_argument_commitments.len() {
                        let c: E::Fr = transcript.get_challenge_scalar();
                        wellformedness_challenges.push(c);
                    }

                    let d = srs.d;
                    let n = 3*self.n + 1; // same as for grand products

                    let alpha_x_d_precomp = srs.h_positive_x_alpha[d].prepare();
                    // TODO: not strictly required
                    assert!(n < d);
                    let d_minus_n = d - n;
                    let alpha_x_n_minus_d_precomp = srs.h_negative_x_alpha[d_minus_n].prepare();
                    let mut h_prep = srs.h_positive_x[0];
                    h_prep.negate();
                    let h_prep = h_prep.prepare();

                    let a = multiexp(
                        wellformedness_argument_commitments.iter(),
                        wellformedness_challenges.iter(),
                    ).into_affine();

                    let r1: E::Fr = self.randomness_source.gen();
                    let r2: E::Fr = self.randomness_source.gen();

                    let mut r = r1;
                    r.add_assign(&r2);
                    let l_r1 = aggregate.signature.grand_product_signature.wellformedness_signature.proof.l.mul(r1.into_repr()).into_affine();
                    let r_r2 = aggregate.signature.grand_product_signature.wellformedness_signature.proof.r.mul(r2.into_repr()).into_affine();

                    let a_r = a.mul(r.into_repr()).into_affine();

                    let valid = E::final_exponentiation(&E::miller_loop(&[
                            (&a_r.prepare(), &h_prep),
                            (&l_r1.prepare(), &alpha_x_d_precomp),
                            (&r_r2.prepare(), &alpha_x_n_minus_d_precomp)
                        ])).unwrap() == E::Fqk::one();

                    assert!(valid, "wellformedness argument must be valid");
                }

            }

            szw
        };

        {
            let random: E::Fr = self.randomness_source.gen();

            self.batch.add_opening(aggregate.opening, random, w);
            self.batch.add_commitment(aggregate.c, random);
            self.batch.add_opening_value(szw, random);
        }

        for ((opening, value), &y) in aggregate.c_openings.iter().zip(y_values.iter()) {
            let random: E::Fr = self.randomness_source.gen();

            self.batch.add_opening(*opening, random, y);
            self.batch.add_commitment(aggregate.c, random);
            self.batch.add_opening_value(*value, random);
        }

        let random: E::Fr = self.randomness_source.gen();

        let mut expected_value = E::Fr::zero();
        for ((_, advice), c_opening) in proofs.iter().zip(aggregate.c_openings.iter()) {
            let mut r: E::Fr = transcript.get_challenge_scalar();

            // expected value of the later opening
            {
                let mut tmp = c_opening.1;
                tmp.mul_assign(&r);
                expected_value.add_assign(&tmp);
            }

            r.mul_assign(&random);

            self.batch.add_commitment(advice.s, r);
        }

        self.batch.add_opening_value(expected_value, random);
        self.batch.add_opening(aggregate.s_opening, random, z);
    }

    /// Caller must ensure to add aggregate after adding a proof
    pub fn add_proof_with_advice(
        &mut self,
        proof: &Proof<E>,
        inputs: &[E::Fr],
        advice: &SxyAdvice<E>,
    )
    {
        let mut z = None;

        self.add_proof(proof, inputs, |_z, _y| {
            z = Some(_z);
            Some(advice.szy)
        });

        let z = z.unwrap();

        // We need to open up SxyAdvice.s at z using SxyAdvice.opening
        let mut transcript = Transcript::new(&[]);
        transcript.commit_point(&advice.opening);
        transcript.commit_point(&advice.s);
        transcript.commit_scalar(&advice.szy);
        let random: E::Fr = self.randomness_source.gen();

        self.batch.add_opening(advice.opening, random, z);
        self.batch.add_commitment(advice.s, random);
        self.batch.add_opening_value(advice.szy, random);
    }

    pub fn add_proof<F>(
        &mut self,
        proof: &Proof<E>,
        inputs: &[E::Fr],
        sxy: F
    )
        where F: FnOnce(E::Fr, E::Fr) -> Option<E::Fr>
    {
        let mut transcript = Transcript::new(&[]);

        transcript.commit_point(&proof.r);

        let y: E::Fr = transcript.get_challenge_scalar();

        transcript.commit_point(&proof.t);

        let z: E::Fr = transcript.get_challenge_scalar();

        transcript.commit_scalar(&proof.rz);
        transcript.commit_scalar(&proof.rzy);

        let r1: E::Fr = transcript.get_challenge_scalar();

        transcript.commit_point(&proof.z_opening);
        transcript.commit_point(&proof.zy_opening);

        // First, the easy one. Let's open up proof.r at zy, using proof.zy_opening
        // as the evidence and proof.rzy as the opening.
        {
            let random: E::Fr = self.randomness_source.gen();
            let mut zy = z;
            zy.mul_assign(&y);
            self.batch.add_opening(proof.zy_opening, random, zy);
            self.batch.add_commitment_max_n(proof.r, random);
            self.batch.add_opening_value(proof.rzy, random);
        }

        // Now we need to compute t(z, y) with what we have. Let's compute k(y).
        let mut ky = E::Fr::zero();
        for (exp, input) in self.k_map.iter().zip(Some(E::Fr::one()).iter().chain(inputs.iter())) {
            let mut term = y.pow(&[(*exp + self.n) as u64]);
            term.mul_assign(input);
            ky.add_assign(&term);
        }

        // Compute s(z, y)
        let szy = sxy(z, y).unwrap_or_else(|| {
            let mut tmp = SxEval::new(y, self.n);
            S::synthesize(&mut tmp, &self.circuit).unwrap(); // TODO

            tmp.finalize(z)

            // let mut tmp = SyEval::new(z, self.n, self.q);
            // S::synthesize(&mut tmp, &self.circuit).unwrap(); // TODO

            // tmp.finalize(y)
        });

        // Finally, compute t(z, y)
        // t(z, y) = (r(z, y) + s(z,y))*r(z, 1) - k(y)
        let mut tzy = proof.rzy;
        tzy.add_assign(&szy);
        tzy.mul_assign(&proof.rz);
        tzy.sub_assign(&ky);

        // We open these both at the same time by keeping their commitments
        // linearly independent (using r1).
        {
            let mut random: E::Fr = self.randomness_source.gen();

            self.batch.add_opening(proof.z_opening, random, z);
            self.batch.add_opening_value(tzy, random);
            self.batch.add_commitment(proof.t, random);

            random.mul_assign(&r1);

            self.batch.add_opening_value(proof.rz, random);
            self.batch.add_commitment_max_n(proof.r, random);
        }
    }

    pub fn get_k_map(&self) -> Vec<usize> {
        return self.k_map.clone();
    }

    pub fn get_n(&self) -> usize {
        return self.n;
    }

    pub fn get_q(&self) -> usize {
        return self.q;
    }

    pub fn check_all(self) -> bool {
        self.batch.check_all()
    }
}

// /// Check multiple proofs without aggregation. Verifier's work is 
// /// not succint due to `S(X, Y)` evaluation
// pub fn verify_proofs<E: Engine, C: Circuit<E>, S: SynthesisDriver, R: Rng>(
//     proofs: &[Proof<E>],
//     inputs: &[Vec<E::Fr>],
//     circuit: C,
//     rng: R,
//     params: &Parameters<E>,
// ) -> Result<bool, SynthesisError> {
//     verify_proofs_on_srs::<E, C, S, R>(proofs, inputs, circuit, rng, &params.srs)
// }

// /// Check multiple proofs without aggregation. Verifier's work is 
// /// not succint due to `S(X, Y)` evaluation
// pub fn verify_proofs_on_srs<E: Engine, C: Circuit<E>, S: SynthesisDriver, R: Rng>(
//     proofs: &[Proof<E>],
//     inputs: &[Vec<E::Fr>],
//     circuit: C,
//     rng: R,
//     srs: &SRS<E>,
// ) -> Result<bool, SynthesisError> {
//     let mut verifier = MultiVerifier::<E, C, S, R>::new(circuit, srs, rng)?;
//     let expected_inputs_size = verifier.get_k_map().len() - 1;
//     for (proof, inputs) in proofs.iter().zip(inputs.iter()) {
//         if inputs.len() != expected_inputs_size {
//             return Err(SynthesisError::Unsatisfiable);
//         }
//         verifier.add_proof(proof, &inputs, |_, _| None);
//     }

//     Ok(verifier.check_all())
// }

// /// Check multiple proofs with aggregation. Verifier's work is 
// /// not succint due to `S(X, Y)` evaluation
// pub fn verify_aggregate<E: Engine, C: Circuit<E>, S: SynthesisDriver,R: Rng>(
//     proofs: &[(Proof<E>, SxyAdvice<E>)],
//     aggregate: &Aggregate<E>,
//     inputs: &[Vec<E::Fr>],
//     circuit: C,
//     rng: R,
//     params: &Parameters<E>,
// ) -> Result<bool, SynthesisError> {
//     verify_aggregate_on_srs::<E, C, S, R>(proofs, aggregate, inputs, circuit, rng, &params.srs)
// }

// /// Check multiple proofs with aggregation. Verifier's work is 
// /// not succint due to `S(X, Y)` evaluation
// pub fn verify_aggregate_on_srs<E: Engine, C: Circuit<E>, S: SynthesisDriver, R: Rng>(
//     proofs: &[(Proof<E>, SxyAdvice<E>)],
//     aggregate: &Aggregate<E>,
//     inputs: &[Vec<E::Fr>],
//     circuit: C,
//     rng: R,
//     srs: &SRS<E>,
// ) -> Result<bool, SynthesisError> {
//     let mut verifier = MultiVerifier::<E, C, S, R>::new(circuit, srs, rng)?;
//     let expected_inputs_size = verifier.get_k_map().len() - 1;
//     for ((proof, advice), inputs) in proofs.iter().zip(inputs.iter()) {
//         if inputs.len() != expected_inputs_size {
//             return Err(SynthesisError::Unsatisfiable);
//         }
//         verifier.add_proof_with_advice(proof, &inputs, &advice);
//     }
//     verifier.add_aggregate(proofs, aggregate);

//     Ok(verifier.check_all())
// }

