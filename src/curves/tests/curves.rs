use rand;
use super::super::{Engine, Field, PrimeField, Curve, CurveAffine};

fn random_test_mixed_addition<E: Engine, G: Curve<E>>(e: &E)
{
    let rng = &mut rand::thread_rng();

    // affine is zero
    {
        let a = G::zero(e).to_affine(e);
        let mut b = G::random(e, rng);
        let bcpy = b;

        b.add_assign_mixed(e, &a);

        assert!(bcpy.is_equal(e, &b));
        assert_eq!(bcpy.to_affine(e), b.to_affine(e));
    }

    // self is zero
    {
        let a = G::random(e, rng).to_affine(e);
        let mut b = G::zero(e);
        let acpy = a.to_jacobian(e);

        b.add_assign_mixed(e, &a);

        assert!(acpy.is_equal(e, &b));
        assert_eq!(acpy.to_affine(e), b.to_affine(e));
    }

    // both are zero
    {
        let a = G::zero(e).to_affine(e);
        let mut b = G::zero(e);
        let acpy = a.to_jacobian(e);

        b.add_assign_mixed(e, &a);

        assert!(acpy.is_equal(e, &b));
        assert_eq!(acpy.to_affine(e), b.to_affine(e));
    }

    // one is negative of the other
    {
        let a = G::random(e, rng);
        let mut b = a;
        b.negate(e);
        let a = a.to_affine(e);

        b.add_assign_mixed(e, &a);
        assert!(b.is_zero());
        assert_eq!(b.to_affine(e), G::zero(e).to_affine(e));
    }

    // doubling case
    {
        let a = G::random(e, rng);
        let b = a.to_affine(e);
        let mut acpy = a;
        acpy.add_assign_mixed(e, &b);

        let mut t = a;
        t.double(e);
        assert!(acpy.is_equal(e, &t));
    }

    for _ in 0..100 {
        let mut x = G::random(e, rng);
        let mut y = x;
        let b = G::random(e, rng);
        let baffine = b.to_affine(e);

        x.add_assign(e, &b);
        y.add_assign_mixed(e, &baffine);

        assert!(x.is_equal(e, &y));
    }
}

fn random_test_addition<E: Engine, G: Curve<E>>(e: &E) {
    let rng = &mut rand::thread_rng();

    for _ in 0..50 {
        let r1 = G::random(e, rng);
        let r2 = G::random(e, rng);
        let r3 = G::random(e, rng);

        {
            let mut tmp1 = r1;
            tmp1.add_assign(e, &r2);
            tmp1.add_assign(e, &r3);

            let mut tmp2 = r2;
            tmp2.add_assign(e, &r3);
            tmp2.add_assign(e, &r1);

            assert!(tmp1.is_equal(e, &tmp2));
        }

        {
            let mut tmp = r1;
            tmp.add_assign(e, &r2);
            tmp.add_assign(e, &r3);
            tmp.sub_assign(e, &r1);
            tmp.sub_assign(e, &r2);
            tmp.sub_assign(e, &r3);

            assert!(tmp.is_zero());
        }
    }
}

fn random_test_doubling<E: Engine, G: Curve<E>>(e: &E) {
    let rng = &mut rand::thread_rng();

    for _ in 0..50 {
        let r1 = G::random(e, rng);
        let r2 = G::random(e, rng);
        let ti = E::Fr::from_str(e, "2").unwrap().inverse(e).unwrap();

        {
            let mut tmp_1 = r1;
            tmp_1.add_assign(e, &r2);
            tmp_1.add_assign(e, &r1);

            let mut tmp_2 = r1;
            tmp_2.double(e);
            tmp_2.add_assign(e, &r2);

            assert!(tmp_1.is_equal(e, &tmp_2));
        }

        {
            let mut tmp = r1;
            tmp.double(e);
            tmp.mul_assign(e, &ti);

            assert!(tmp.is_equal(e, &r1));
        }
    }
}

fn random_test_dh<E: Engine, G: Curve<E>>(e: &E) {
    let rng = &mut rand::thread_rng();

    for _ in 0..50 {
        let alice_sk = E::Fr::random(e, rng);
        let bob_sk = E::Fr::random(e, rng);

        let mut alice_pk = G::one(e);
        alice_pk.mul_assign(e, &alice_sk);
        let mut bob_pk = G::one(e);
        bob_pk.mul_assign(e, &bob_sk);

        let mut alice_shared = bob_pk;
        alice_shared.mul_assign(e, &alice_sk);
        let mut bob_shared = alice_pk;
        bob_shared.mul_assign(e, &bob_sk);

        assert!(alice_shared.is_equal(e, &bob_shared));
    }
}

fn random_mixed_addition<E: Engine, G: Curve<E>>(e: &E) {
    let rng = &mut rand::thread_rng();

    for _ in 0..50 {
        let a = G::random(e, rng);

        let mut res = a;
        res.double(e);

        let affine = a.to_affine(e);
        let mut jacobian = affine.to_jacobian(e);
        jacobian.double(e);

        assert!(jacobian.is_equal(e, &res));
    }
}

fn random_test_equality<E: Engine, G: Curve<E>>(e: &E) {
    let rng = &mut rand::thread_rng();

    for _ in 0..50 {
        let begin = G::random(e, rng);

        let mut acc = begin;

        let a = E::Fr::random(e, rng);
        let b = G::random(e, rng);
        let c = E::Fr::random(e, rng);
        let d = G::random(e, rng);

        for _ in 0..10 {
            acc.mul_assign(e, &a);
            acc.negate(e);
            acc.add_assign(e, &b);
            acc.mul_assign(e, &c);
            acc.negate(e);
            acc.sub_assign(e, &d);
            acc.double(e);
        }

        assert!(!acc.is_equal(e, &begin));

        let ai = a.inverse(e).unwrap();
        let ci = c.inverse(e).unwrap();
        let ti = E::Fr::from_str(e, "2").unwrap().inverse(e).unwrap();

        for _ in 0..10 {
            acc.mul_assign(e, &ti);
            acc.add_assign(e, &d);
            acc.negate(e);
            acc.mul_assign(e, &ci);
            acc.sub_assign(e, &b);
            acc.negate(e);
            acc.mul_assign(e, &ai);
        }

        assert!(acc.is_equal(e, &begin));
    }
}

pub fn test_curve<E: Engine, G: Curve<E>>(e: &E) {
    {
        let rng = &mut rand::thread_rng();
        let mut g = G::random(e, rng);
        let order = <E::Fr as PrimeField<E>>::char(e);
        g.mul_assign(e, &order);

        assert!(g.is_zero());
    }
    {
        let rng = &mut rand::thread_rng();
        let mut neg1 = E::Fr::one(e);
        neg1.negate(e);
        for _ in 0..1000 {
            let orig = G::random(e, rng);
            let mut a = orig;
            a.mul_assign(e, &neg1);
            assert!(!a.is_zero());
            a.add_assign(e, &orig);
            assert!(a.is_zero());
        }
    }
    {
        let mut o = G::one(e);
        o.sub_assign(e, &G::one(e));
        assert!(o.is_zero());
    }
    {
        let mut o = G::one(e);
        o.add_assign(e, &G::one(e));
        let mut r = G::one(e);
        r.mul_assign(e, &E::Fr::from_str(e, "2").unwrap());
        assert!(o.is_equal(e, &r));
    }
    {
        let mut z = G::zero(e);
        assert!(z.is_zero());
        z.double(e);
        assert!(z.is_zero());

        let zaffine = z.to_affine(e);
        let zjacobian = zaffine.to_jacobian(e);

        assert!(zjacobian.is_zero());
    }

    random_test_equality::<E, G>(e);
    random_test_dh::<E, G>(e);
    random_test_doubling::<E, G>(e);
    random_test_addition::<E, G>(e);
    random_mixed_addition::<E, G>(e);
    random_test_mixed_addition::<E, G>(e);
}
