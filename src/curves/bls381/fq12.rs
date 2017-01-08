use super::{Bls381, Fq2, Fq6};
use rand;
use super::Field;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Fq12 {
    pub c0: Fq6,
    pub c1: Fq6
}

impl Fq12 {
    pub fn unitary_inverse(&mut self, e: &Bls381)
    {
        self.c1.negate(e);
    }

    pub fn mul_by_015(
        &mut self,
        e: &Bls381,
        a: &Fq2,
        b: &Fq2,
        c: &Fq2
    )
    {
        let mut aa = self.c0;
        aa.mul_by_01(e, a, b);
        let mut bb = self.c1;
        bb.mul_by_1(e, c);
        let mut o = *b;
        o.add_assign(e, &c);
        self.c1.add_assign(e, &self.c0);
        self.c1.mul_by_01(e, a, &o);
        self.c1.sub_assign(e, &aa);
        self.c1.sub_assign(e, &bb);
        self.c0 = bb;
        self.c0.mul_by_nonresidue(e);
        self.c0.add_assign(e, &aa);
    }
}

impl Field<Bls381> for Fq12
{
    fn zero() -> Self {
        Fq12 {
            c0: Fq6::zero(),
            c1: Fq6::zero()
        }
    }

    fn one(engine: &Bls381) -> Self {
        Fq12 {
            c0: Fq6::one(engine),
            c1: Fq6::zero()
        }
    }

    fn random<R: rand::Rng>(engine: &Bls381, rng: &mut R) -> Self {
        Fq12 {
            c0: Fq6::random(engine, rng),
            c1: Fq6::random(engine, rng)
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
        self.c0.frobenius_map(e, power);
        self.c1.frobenius_map(e, power);

        self.c1.c0.mul_assign(e, &e.frobenius_coeff_fq12[power % 12]);
        self.c1.c1.mul_assign(e, &e.frobenius_coeff_fq12[power % 12]);
        self.c1.c2.mul_assign(e, &e.frobenius_coeff_fq12[power % 12]);
    }

    fn square(&mut self, e: &Bls381) {
        let mut ab = self.c0;
        ab.mul_assign(e, &self.c1);
        let mut c0c1 = self.c0;
        c0c1.add_assign(e, &self.c1);
        let mut c0 = self.c1;
        c0.mul_by_nonresidue(e);
        c0.add_assign(e, &self.c0);
        c0.mul_assign(e, &c0c1);
        c0.sub_assign(e, &ab);
        self.c1 = ab;
        self.c1.add_assign(e, &ab);
        ab.mul_by_nonresidue(e);
        c0.sub_assign(e, &ab);
        self.c0 = c0;
    }

    fn mul_assign(&mut self, e: &Bls381, other: &Self) {
        let mut aa = self.c0;
        aa.mul_assign(e, &other.c0);
        let mut bb = self.c1;
        bb.mul_assign(e, &other.c1);
        let mut o = other.c0;
        o.add_assign(e, &other.c1);
        self.c1.add_assign(e, &self.c0);
        self.c1.mul_assign(e, &o);
        self.c1.sub_assign(e, &aa);
        self.c1.sub_assign(e, &bb);
        self.c0 = bb;
        self.c0.mul_by_nonresidue(e);
        self.c0.add_assign(e, &aa);
    }

    fn inverse(&self, e: &Bls381) -> Option<Self> {
        let mut c0s = self.c0;
        c0s.square(e);
        let mut c1s = self.c1;
        c1s.square(e);
        c1s.mul_by_nonresidue(e);
        c0s.sub_assign(e, &c1s);

        c0s.inverse(e).map(|t| {
            let mut tmp = Fq12 {
                c0: t,
                c1: t
            };
            tmp.c0.mul_assign(e, &self.c0);
            tmp.c1.mul_assign(e, &self.c1);
            tmp.c1.negate(e);

            tmp
        })
    }
}
