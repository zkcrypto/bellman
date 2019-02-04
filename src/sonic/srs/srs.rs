use ff::{Field, PrimeField};
use pairing::{CurveAffine, CurveProjective, Engine, Wnaf};

pub struct SRS<E: Engine> {
    pub d: usize,

    // g^{x^0}, g^{x^{-1}}, g^{x^{-2}}, ..., g^{x^{-d}}
    pub g_negative_x: Vec<E::G1Affine>,

    // g^{x^0}, g^{x^{1}}, g^{x^{2}}, ..., g^{x^{d}}
    pub g_positive_x: Vec<E::G1Affine>,

    // g^{x^0}, g^{x^{-1}}, g^{x^{-2}}, ..., g^{x^{-d}}
    pub h_negative_x: Vec<E::G2Affine>,

    // g^{x^0}, g^{x^{1}}, g^{x^{2}}, ..., g^{x^{d}}
    pub h_positive_x: Vec<E::G2Affine>,

    // alpha*(g^{x^{-1}}, g^{x^{-2}}, ..., g^{x^{-d}})
    pub g_negative_x_alpha: Vec<E::G1Affine>,

    // alpha*(g^{x^{1}}, g^{x^{2}}, ..., g^{x^{d}})
    pub g_positive_x_alpha: Vec<E::G1Affine>,

    // alpha*(h^{x^0}, h^{x^{-1}}, g^{x^{-2}}, ..., g^{x^{-d}})
    pub h_negative_x_alpha: Vec<E::G2Affine>,

    // alpha*(h^{x^0}, g^{x^{1}}, g^{x^{2}}, ..., g^{x^{d}})
    pub h_positive_x_alpha: Vec<E::G2Affine>,
}

impl<E: Engine> SRS<E> {
    pub fn dummy(d: usize, _: E::Fr, _: E::Fr) -> Self {
        SRS {
            d: d,
            g_negative_x: vec![E::G1Affine::one(); d + 1],
            g_positive_x: vec![E::G1Affine::one(); d + 1],

            h_negative_x: vec![E::G2Affine::one(); d + 1],
            h_positive_x: vec![E::G2Affine::one(); d + 1],

            g_negative_x_alpha: vec![E::G1Affine::one(); d],
            g_positive_x_alpha: vec![E::G1Affine::one(); d],

            h_negative_x_alpha: vec![E::G2Affine::one(); d + 1],
            h_positive_x_alpha: vec![E::G2Affine::one(); d + 1],
        }
    }

    pub fn new(d: usize, x: E::Fr, alpha: E::Fr) -> Self {
        let mut g1 = Wnaf::new();
        let mut g1 = g1.base(E::G1::one(), d * 4);
        let mut g2 = Wnaf::new();
        let mut g2 = g2.base(E::G2::one(), d * 4);

        fn table<C: CurveAffine>(
            mut cur: C::Scalar,
            step: C::Scalar,
            num: usize,
            table: &mut Wnaf<usize, &[C::Projective], &mut Vec<i64>>,
        ) -> Vec<C> {
            let mut v = vec![];
            for _ in 0..num {
                v.push(table.scalar(cur.into_repr()));
                cur.mul_assign(&step);
            }
            C::Projective::batch_normalization(&mut v);
            let v = v.into_iter().map(|e| e.into_affine()).collect();
            v
        }

        let x_inv = x.inverse().unwrap();

        let mut x_alpha = x;
        x_alpha.mul_assign(&alpha);

        let mut inv_x_alpha = x_inv;
        inv_x_alpha.mul_assign(&alpha);

        SRS {
            d: d,
            g_negative_x: table(E::Fr::one(), x_inv, d + 1, &mut g1),
            g_positive_x: table(E::Fr::one(), x, d + 1, &mut g1),

            h_negative_x: table(E::Fr::one(), x_inv, d + 1, &mut g2),
            h_positive_x: table(E::Fr::one(), x, d + 1, &mut g2),

            g_negative_x_alpha: table(inv_x_alpha, x_inv, d, &mut g1),
            g_positive_x_alpha: table(x_alpha, x, d, &mut g1),

            h_negative_x_alpha: table(alpha, x_inv, d + 1, &mut g2),
            h_positive_x_alpha: table(alpha, x, d + 1, &mut g2),
        }
    }
}
