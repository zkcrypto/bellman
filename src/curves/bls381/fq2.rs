use super::{Bls381, Fq};
use rand;
use super::{Field, SqrtField};

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Fq2 {
    pub c0: Fq,
    pub c1: Fq
}

impl Fq2 {
    pub fn mul_by_nonresidue(&mut self, e: &Bls381) {
        let t0 = self.c0;
        self.c0.sub_assign(e, &self.c1);
        self.c1.add_assign(e, &t0);
    }
}

impl SqrtField<Bls381> for Fq2 {
    fn sqrt(&self, engine: &Bls381) -> Option<Self> {
        // Algorithm 9, https://eprint.iacr.org/2012/685.pdf

        if self.is_zero() {
            return Some(Self::zero());
        } else {
            let mut a1 = self.pow(engine, &engine.fqparams.modulus_minus_3_over_4);
            let mut alpha = a1;
            alpha.square(engine);
            alpha.mul_assign(engine, self);
            let mut a0 = alpha.pow(engine, &engine.fqparams.modulus);
            a0.mul_assign(engine, &alpha);

            let mut neg1 = Self::one(engine);
            neg1.negate(engine);

            if a0 == neg1 {
                None
            } else {
                a1.mul_assign(engine, self);

                if alpha == neg1 {
                    a1.mul_assign(engine, &Fq2{c0: Fq::zero(), c1: Fq::one(engine)});
                } else {
                    alpha.add_assign(engine, &Fq2::one(engine));
                    alpha = alpha.pow(engine, &engine.fqparams.modulus_minus_1_over_2);
                    a1.mul_assign(engine, &alpha);
                }

                Some(a1)
            }
        }
    }
}

impl Field<Bls381> for Fq2
{
    fn zero() -> Self {
        Fq2 {
            c0: Fq::zero(),
            c1: Fq::zero()
        }
    }

    fn one(engine: &Bls381) -> Self {
        Fq2 {
            c0: Fq::one(engine),
            c1: Fq::zero()
        }
    }

    fn random<R: rand::Rng>(engine: &Bls381, rng: &mut R) -> Self {
        Fq2 {
            c0: Fq::random(engine, rng),
            c1: Fq::random(engine, rng)
        }
    }

    fn is_zero(&self) -> bool {
        self.c0.is_zero() && self.c1.is_zero()
    }

    fn double(&mut self, engine: &Bls381) {
        self.c0.double(engine);
        self.c1.double(engine);
    }

    fn negate(&mut self, engine: &Bls381) {
        self.c0.negate(engine);
        self.c1.negate(engine);
    }

    fn add_assign(&mut self, engine: &Bls381, other: &Self) {
        self.c0.add_assign(engine, &other.c0);
        self.c1.add_assign(engine, &other.c1);
    }

    fn sub_assign(&mut self, engine: &Bls381, other: &Self) {
        self.c0.sub_assign(engine, &other.c0);
        self.c1.sub_assign(engine, &other.c1);
    }

    fn frobenius_map(&mut self, e: &Bls381, power: usize)
    {
        self.c1.mul_assign(e, &e.frobenius_coeff_fq2[power % 2]);
    }

    fn square(&mut self, engine: &Bls381) {
        let mut ab = self.c0;
        ab.mul_assign(engine, &self.c1);
        let mut c0c1 = self.c0;
        c0c1.add_assign(engine, &self.c1);
        let mut c0 = self.c1;
        c0.negate(engine);
        c0.add_assign(engine, &self.c0);
        c0.mul_assign(engine, &c0c1);
        c0.sub_assign(engine, &ab);
        self.c1 = ab;
        self.c1.add_assign(engine, &ab);
        c0.add_assign(engine, &ab);
        self.c0 = c0;
    }

    fn mul_assign(&mut self, engine: &Bls381, other: &Self) {
        let mut aa = self.c0;
        aa.mul_assign(engine, &other.c0);
        let mut bb = self.c1;
        bb.mul_assign(engine, &other.c1);
        let mut o = other.c0;
        o.add_assign(engine, &other.c1);
        self.c1.add_assign(engine, &self.c0);
        self.c1.mul_assign(engine, &o);
        self.c1.sub_assign(engine, &aa);
        self.c1.sub_assign(engine, &bb);
        self.c0 = aa;
        self.c0.sub_assign(engine, &bb);
    }

    fn inverse(&self, engine: &Bls381) -> Option<Self> {
        let mut t1 = self.c1;
        t1.square(engine);
        let mut t0 = self.c0;
        t0.square(engine);
        t0.add_assign(engine, &t1);
        t0.inverse(engine).map(|t| {
            let mut tmp = Fq2 {
                c0: self.c0,
                c1: self.c1
            };
            tmp.c0.mul_assign(engine, &t);
            tmp.c1.mul_assign(engine, &t);
            tmp.c1.negate(engine);

            tmp
        })
    }
}
