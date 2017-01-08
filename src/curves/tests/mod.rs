use super::{Engine, Group, GroupAffine, Field, PrimeField};
use rand;

mod fields;
mod groups;

fn test_multiexp<E: Engine, G: Group<E>>(e: &E) {
    fn naiveexp<E: Engine, G: Group<E>>(e: &E, g: &[G::Affine], s: &[E::Fr]) -> G
    {
        assert!(g.len() == s.len());

        let mut expected = G::zero(e);
        for (g, s) in g.iter().zip(s.iter()) {
            expected.add_assign(e, &g.mul(e, s));
        }

        expected
    }

    {
        let rng = &mut rand::thread_rng();

        let g: Vec<G::Affine> = (0..1000).map(|_| G::random(e, rng).to_affine(e)).collect();
        let s: Vec<E::Fr> = (0..1000).map(|_| E::Fr::random(e, rng)).collect();

        let naive = naiveexp::<E, G>(e, &g, &s);
        let multi = e.multiexp::<G>(&g, &s);

        assert!(naive.is_equal(e, &multi));
        assert!(multi.is_equal(e, &naive));
    }

    {
        let rng = &mut rand::thread_rng();
        let g: Vec<G::Affine> = (0..2).map(|_| G::random(e, rng).to_affine(e)).collect();
        let s = vec![E::Fr::from_str(e, "3435973836800000000000000000000000").unwrap(), E::Fr::from_str(e, "3435973836700000000000000000000000").unwrap()];

        let naive = naiveexp::<E, G>(e, &g, &s);
        let multi = e.multiexp::<G>(&g, &s);

        assert!(naive.is_equal(e, &multi));
        assert!(multi.is_equal(e, &naive));
    }
}

fn test_bilinearity<E: Engine>(e: &E) {
    let rng = &mut rand::thread_rng();

    let a = E::G1::random(e, rng);
    let b = E::G2::random(e, rng);
    let s = E::Fr::random(e, rng);

    let mut a_s = a;
    a_s.mul_assign(e, &s);

    let mut b_s = b;
    b_s.mul_assign(e, &s);

    let test1 = e.pairing(&a_s, &b);
    assert!(test1 != E::Fqk::one(e));
    let test2 = e.pairing(&a, &b_s);
    assert_eq!(test1, test2);
    
    let mut test4 = e.pairing(&a, &b);
    assert!(test4 != test1);
    test4 = test4.pow(e, &s);
    assert_eq!(test1, test4);
}

fn test_multimiller<E: Engine>(e: &E) {
    let rng = &mut rand::thread_rng();

    let a1 = E::G1::random(e, rng);
    let a2 = E::G2::random(e, rng);

    let b1 = E::G1::random(e, rng);
    let b2 = E::G2::random(e, rng);

    let mut p1 = e.pairing(&a1, &a2);
    let p2 = e.pairing(&b1, &b2);
    p1.mul_assign(e, &p2);

    let mm = e.final_exponentiation(&e.miller_loop(
        [
            (&a1.prepare(e), &a2.prepare(e)),
            (&b1.prepare(e), &b2.prepare(e))
        ].into_iter()
    ));

    assert_eq!(p1, mm);
}

pub fn test_engine<E: Engine>() {
    let engine = E::new();

    fields::test_prime_field::<E, E::Fq>(&engine);
    fields::test_prime_field::<E, E::Fr>(&engine);
    fields::test_sqrt_field::<E, E::Fq>(&engine);
    fields::test_sqrt_field::<E, E::Fr>(&engine);
    fields::test_sqrt_field::<E, E::Fqe>(&engine);

    fields::test_field::<E, E::Fq>(&engine);
    fields::test_field::<E, E::Fr>(&engine);
    fields::test_field::<E, E::Fqe>(&engine);
    fields::test_field::<E, E::Fqk>(&engine);

    groups::test_group::<E, E::G1>(&engine);
    groups::test_group::<E, E::G2>(&engine);

    test_bilinearity(&engine);
    test_multimiller(&engine);
    test_frobenius(&engine);
    test_multiexp::<E, E::G1>(&engine);
    test_multiexp::<E, E::G2>(&engine);
}

fn test_frobenius<E: Engine>(e: &E) {
    let rng = &mut rand::thread_rng();
    let modulus = E::Fq::char(e);

    let a = E::Fqk::random(e, rng);
    let mut acpy = a;
    acpy.frobenius_map(e, 0);
    assert_eq!(acpy, a);

    let mut a_q = a.pow(e, &modulus);

    for p in 1..12 {
        acpy = a;
        acpy.frobenius_map(e, p);

        assert_eq!(acpy, a_q);

        a_q = a_q.pow(e, &modulus);
    }
}
