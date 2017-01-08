use rand::{self, Rng};
use super::super::{Engine, Field, SqrtField, PrimeField};

fn inversion_tests<E: Engine, F: Field<E>, R: Rng>(e: &E, rng: &mut R) {
    let mut a = F::one(e);
    for _ in 0..10000 {
        let mut b = a.inverse(e).unwrap();
        b.mul_assign(e, &a);
        assert_eq!(b, F::one(e));
        a.add_assign(e, &F::one(e));
    }
    a = F::one(e);
    a.negate(e);
    for _ in 0..10000 {
        let mut b = a.inverse(e).unwrap();
        b.mul_assign(e, &a);
        assert_eq!(b, F::one(e));
        a.sub_assign(e, &F::one(e));
    }
    a = F::zero();
    assert!(a.inverse(e).is_none());
    for _ in 0..10000 {
        let r = F::random(e, rng);
        assert!(!r.is_zero());
        let mut rinv = r.inverse(e).unwrap();
        rinv.mul_assign(e, &r);
        assert_eq!(rinv, F::one(e));
    }
}

fn expansion_tests<E: Engine, F: Field<E>, R: Rng>(e: &E, rng: &mut R) {
    for _ in 0..100 {
        let a = F::random(e, rng);
        let b = F::random(e, rng);
        let c = F::random(e, rng);
        let d = F::random(e, rng);

        let lhs;
        {
            let mut t0 = a;
            t0.add_assign(e, &b);
            let mut t1 = c;
            t1.add_assign(e, &d);
            t0.mul_assign(e, &t1);
            lhs = t0;
        }

        let rhs;
        {
            let mut t0 = a;
            t0.mul_assign(e, &c);
            let mut t1 = b;
            t1.mul_assign(e, &c);
            let mut t2 = a;
            t2.mul_assign(e, &d);
            let mut t3 = b;
            t3.mul_assign(e, &d);
            t0.add_assign(e, &t1);
            t0.add_assign(e, &t2);
            t0.add_assign(e, &t3);
            rhs = t0;
        }

        assert_eq!(lhs, rhs);
    }
}

fn squaring_tests<E: Engine, F: Field<E>, R: Rng>(e: &E, rng: &mut R) {
    for _ in 0..100 {
        let mut a = F::random(e, rng);
        let mut b = a;
        b.mul_assign(e, &a);
        a.square(e);

        assert_eq!(a, b);
    }

    let mut cur = F::zero();
    for _ in 0..100 {
        let mut a = cur;
        a.square(e);
        let mut b = cur;
        b.mul_assign(e, &cur);

        assert_eq!(a, b);

        cur.add_assign(e, &F::one(e));
    }
}

fn operation_tests<E: Engine, F: Field<E>, R: Rng>(e: &E, rng: &mut R) {
    {
        let mut acc = F::zero();
        for _ in 0..1000 {
            let mut a = acc;
            a.negate(e);
            a.add_assign(e, &acc);

            assert_eq!(a, F::zero());
            acc.add_assign(e, &F::one(e));
        }
    }
    {
        for _ in 0..1000 {
            let mut a = F::random(e, rng);
            let mut at = a;
            let mut b = F::random(e, rng);

            a.sub_assign(e, &b);
            b.negate(e);
            at.add_assign(e, &b);

            assert_eq!(a, at);
        }
    }
}

pub fn test_field<E: Engine, F: Field<E>>(e: &E) {
    let rng = &mut rand::thread_rng();

    inversion_tests::<E, F, _>(e, rng);
    expansion_tests::<E, F, _>(e, rng);
    squaring_tests::<E, F, _>(e, rng);
    operation_tests::<E, F, _>(e, rng);
}

pub fn test_sqrt_field<E: Engine, F: SqrtField<E>>(e: &E) {
    const SAMPLES: isize = 10000;

    {
        let mut acc = F::one(e);

        for _ in 0..SAMPLES {
            let mut b = acc;
            b.square(e);
            let mut c = b.sqrt(e).unwrap();
            if c != acc {
                c.negate(e);
            }

            assert_eq!(acc, c);

            acc.add_assign(e, &F::one(e));
        }
    }

    {
        let mut acc = F::one(e);

        for _ in 0..SAMPLES {
            match acc.sqrt(e) {
                Some(mut a) => {
                    a.square(e);

                    assert_eq!(a, acc);
                },
                None => {}
            }

            acc.add_assign(e, &F::one(e));
        }
    }

    {
        let rng = &mut rand::thread_rng();

        for _ in 0..SAMPLES {
            let a = F::random(e, rng);
            let mut b = a;
            b.square(e);
            let mut c = b.sqrt(e).unwrap();
            if c != a {
                c.negate(e);
            }

            assert_eq!(a, c);
        }
    }

    {
        let rng = &mut rand::thread_rng();

        let mut qr: isize = 0;
        let mut nqr: isize = 0;
        for _ in 0..SAMPLES {
            let a = F::random(e, rng);
            match a.sqrt(e) {
                Some(mut b) => {
                    qr += 1;
                    b.square(e);
                    assert_eq!(a, b);
                },
                None => {
                    nqr += 1;
                }
            }
        }

        assert!((qr - nqr < (SAMPLES / 20)) || (qr - nqr > -(SAMPLES / 20)));
    }
}

pub fn test_prime_field<E: Engine, F: PrimeField<E>>(e: &E) {
    let rng = &mut rand::thread_rng();

    for _ in 0..100 {
        let a = F::random(e, rng);
        let b = F::random(e, rng);
        let mut c = a;
        c.mul_assign(e, &b);
        let a = a.into_repr(e);
        let b = b.into_repr(e);
        let expected_a = F::from_repr(e, a).unwrap();
        let expected_b = F::from_repr(e, b).unwrap();
        let mut expected_c = expected_a;
        expected_c.mul_assign(e, &expected_b);
        assert_eq!(c, expected_c);
    }
}
