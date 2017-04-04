use super::*;
use rand::{Rng, thread_rng};

struct RootCircuit<E: Engine> {
    root: E::Fr
}

impl<E: Engine> Circuit<E> for RootCircuit<E> {
    type WitnessMap = RootWitness<E>;

    fn synthesize<CS: ConstraintSystem<E>>(self,
                                           e: &E,
                                           cs: &mut CS)
                                           -> Self::WitnessMap
    {
        let root_var = cs.alloc(self.root);

        let mut cur = root_var;
        let mut cur_val = self.root;

        for _ in 0..99 {
            cur_val.mul_assign(e, &self.root);
            let new = cs.alloc(cur_val);

            cs.enforce(
                LinearCombination::zero(e) + (E::Fr::from_str(e, "3").unwrap(), cur),
                LinearCombination::zero(e) + (E::Fr::from_str(e, "4").unwrap(), root_var),
                LinearCombination::zero(e) + (E::Fr::from_str(e, "12").unwrap(), new),
            );

            cur = new;
        }

        RootWitness {
            num: cur_val,
            num_var: cur
        }
    }
}

struct RootWitness<E: Engine> {
    num: E::Fr,
    num_var: Variable
}

impl<E: Engine> Witness<E> for RootWitness<E> {
    fn synthesize<CS: PublicConstraintSystem<E>>(
        self,
        e: &E,
        cs: &mut CS
    )
    {
        let result_input = cs.alloc_input(self.num);
        cs.enforce(
            LinearCombination::zero(e) + result_input,
            LinearCombination::one(e),
            LinearCombination::zero(e) + self.num_var
        );
    }
}

fn test_snark_system<E: Engine, R: Rng>(
    e: &E,
    rng: &mut R
)
{
    let tau = E::Fr::random(e, rng);
    let alpha = E::Fr::random(e, rng);
    let beta = E::Fr::random(e, rng);
    let gamma = E::Fr::random(e, rng);
    let delta = E::Fr::random(e, rng);

    // create keypair
    let (pk, vk) = {
        let c = RootCircuit {
            root: E::Fr::zero()
        };

        keypair(e, c, &tau, &alpha, &beta, &gamma, &delta)
    };

    // construct proof
    let proof = {
        let r = E::Fr::random(e, rng);
        let s = E::Fr::random(e, rng);

        let c = RootCircuit {
            root: E::Fr::from_str(e, "2").unwrap()
        };

        prove(e, c, &r, &s, &pk).unwrap()
    };

    // prepare verifying key
    let pvk = prepare_verifying_key(e, &vk);

    // verify proof
    assert!(verify(e, |cs| {
        RootWitness {
            num: E::Fr::from_str(e, "1267650600228229401496703205376").unwrap(),
            num_var: cs.alloc(E::Fr::one(e))
        }
    }, &proof, &pvk));

    // verify invalid proof
    assert!(!verify(e, |cs| {
        RootWitness {
            num: E::Fr::from_str(e, "1267650600228229401496703205375").unwrap(),
            num_var: cs.alloc(E::Fr::one(e))
        }
    }, &proof, &pvk));

    // simulate a groth proof with trapdoors
    // ----------------
    // 99: a1 * a0 = l*
    // 100: a0 * 0 = 0
    // 101: a1 * 0 = 0
    // ---
    // u_0(tau) = tau^100
    // u_1(tau) = tau^99 + tau^101
    // v_0(tau) = tau^99
    // v_1(tau) = 0
    // w_0(tau) = 0
    // w_1(tau) = 0
    // ---

    let mut lagrange_coeffs: Vec<E::Fr> = (0..128).map(|i| tau.pow(e, &[i])).collect();

    let d = domain::EvaluationDomain::new(e, 128);
    d.ifft(e, &mut lagrange_coeffs);

    let a = E::Fr::random(e, rng);
    let b = E::Fr::random(e, rng);

    let mut c = a;
    c.mul_assign(e, &b);

    let mut alphabeta = alpha;
    alphabeta.mul_assign(e, &beta);
    c.sub_assign(e, &alphabeta);

    let mut ic = E::Fr::zero();
    {
        let mut ic_i_beta = lagrange_coeffs[100];
        ic_i_beta.mul_assign(e, &beta);

        let mut ic_i_alpha = lagrange_coeffs[99];
        ic_i_alpha.mul_assign(e, &alpha);

        ic_i_beta.add_assign(e, &ic_i_alpha);

        ic.add_assign(e, &ic_i_beta);
    }
    {
        let mut ic_i_beta = lagrange_coeffs[99];
        ic_i_beta.add_assign(e, &lagrange_coeffs[101]);
        ic_i_beta.mul_assign(e, &beta);

        ic_i_beta.mul_assign(e, &E::Fr::from_str(e, "100").unwrap());

        ic.add_assign(e, &ic_i_beta);
    }

    c.sub_assign(e, &ic);
    c.mul_assign(e, &delta.inverse(e).unwrap());

    let mut a_g = E::G1::one(e);
    a_g.mul_assign(e, &a);

    let mut b_g = E::G2::one(e);
    b_g.mul_assign(e, &b);

    let mut c_g = E::G1::one(e);
    c_g.mul_assign(e, &c);

    let fake_proof = Proof {
        a: a_g,
        b: b_g,
        c: c_g
    };

    // verify fake proof
    assert!(verify(e, |cs| {
        RootWitness {
            num: E::Fr::from_str(e, "100").unwrap(),
            num_var: cs.alloc(E::Fr::one(e))
        }
    }, &fake_proof, &pvk));

    // verify fake proof with wrong input
    assert!(!verify(e, |cs| {
        RootWitness {
            num: E::Fr::from_str(e, "101").unwrap(),
            num_var: cs.alloc(E::Fr::one(e))
        }
    }, &fake_proof, &pvk));
}

#[test]
fn groth_with_bls381() {
    use curves::bls381::Bls381;

    let e = &Bls381::new();
    let rng = &mut thread_rng();

    test_snark_system(e, rng);
}
