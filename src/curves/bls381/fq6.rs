use super::{Bls381, Fq2};
use rand;
use super::Field;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Fq6 {
    pub c0: Fq2,
    pub c1: Fq2,
    pub c2: Fq2
}

impl Fq6 {
    pub fn mul_by_nonresidue(&mut self, e: &Bls381) {
        use std::mem::swap;
        swap(&mut self.c0, &mut self.c1);
        swap(&mut self.c0, &mut self.c2);

        self.c0.mul_by_nonresidue(e);
    }

    pub fn mul_by_1(&mut self, e: &Bls381, c1: &Fq2)
    {
        let mut b_b = self.c1;
        b_b.mul_assign(e, c1);

        let mut t1 = *c1;
        {
            let mut tmp = self.c1;
            tmp.add_assign(e, &self.c2);

            t1.mul_assign(e, &tmp);
            t1.sub_assign(e, &b_b);
            t1.mul_by_nonresidue(e);
        }

        let mut t2 = *c1;
        {
            let mut tmp = self.c0;
            tmp.add_assign(e, &self.c1);

            t2.mul_assign(e, &tmp);
            t2.sub_assign(e, &b_b);
        }

        self.c0 = t1;
        self.c1 = t2;
        self.c2 = b_b;
    }

    pub fn mul_by_01(&mut self, e: &Bls381, c0: &Fq2, c1: &Fq2)
    {
        let mut a_a = self.c0;
        let mut b_b = self.c1;
        a_a.mul_assign(e, c0);
        b_b.mul_assign(e, c1);

        let mut t1 = *c1;
        {
            let mut tmp = self.c1;
            tmp.add_assign(e, &self.c2);

            t1.mul_assign(e, &tmp);
            t1.sub_assign(e, &b_b);
            t1.mul_by_nonresidue(e);
            t1.add_assign(e, &a_a);
        }

        let mut t3 = *c0;
        {
            let mut tmp = self.c0;
            tmp.add_assign(e, &self.c2);

            t3.mul_assign(e, &tmp);
            t3.sub_assign(e, &a_a);
            t3.add_assign(e, &b_b);
        }

        let mut t2 = *c0;
        t2.add_assign(e, c1);
        {
            let mut tmp = self.c0;
            tmp.add_assign(e, &self.c1);

            t2.mul_assign(e, &tmp);
            t2.sub_assign(e, &a_a);
            t2.sub_assign(e, &b_b);
        }

        self.c0 = t1;
        self.c1 = t2;
        self.c2 = t3;
    }
}

impl Field<Bls381> for Fq6
{
    fn zero() -> Self {
        Fq6 {
            c0: Fq2::zero(),
            c1: Fq2::zero(),
            c2: Fq2::zero()
        }
    }

    fn one(engine: &Bls381) -> Self {
        Fq6 {
            c0: Fq2::one(engine),
            c1: Fq2::zero(),
            c2: Fq2::zero()
        }
    }

    fn random<R: rand::Rng>(engine: &Bls381, rng: &mut R) -> Self {
        Fq6 {
            c0: Fq2::random(engine, rng),
            c1: Fq2::random(engine, rng),
            c2: Fq2::random(engine, rng)
        }
    }

    fn is_zero(&self) -> bool {
        self.c0.is_zero() && self.c1.is_zero() && self.c2.is_zero()
    }

    fn double(&mut self, engine: &Bls381) {
        self.c0.double(engine);
        self.c1.double(engine);
        self.c2.double(engine);
    }

    fn negate(&mut self, engine: &Bls381) {
        self.c0.negate(engine);
        self.c1.negate(engine);
        self.c2.negate(engine);
    }

    fn add_assign(&mut self, engine: &Bls381, other: &Self) {
        self.c0.add_assign(engine, &other.c0);
        self.c1.add_assign(engine, &other.c1);
        self.c2.add_assign(engine, &other.c2);
    }

    fn sub_assign(&mut self, engine: &Bls381, other: &Self) {
        self.c0.sub_assign(engine, &other.c0);
        self.c1.sub_assign(engine, &other.c1);
        self.c2.sub_assign(engine, &other.c2);
    }

    fn frobenius_map(&mut self, e: &Bls381, power: usize)
    {
        self.c0.frobenius_map(e, power);
        self.c1.frobenius_map(e, power);
        self.c2.frobenius_map(e, power);

        self.c1.mul_assign(e, &e.frobenius_coeff_fq6_c1[power % 6]);
        self.c2.mul_assign(e, &e.frobenius_coeff_fq6_c2[power % 6]);
    }

    fn square(&mut self, e: &Bls381) {
        let mut s0 = self.c0;
        s0.square(e);
        let mut ab = self.c0;
        ab.mul_assign(e, &self.c1);
        let mut s1 = ab;
        s1.double(e);
        let mut s2 = self.c0;
        s2.sub_assign(e, &self.c1);
        s2.add_assign(e, &self.c2);
        s2.square(e);
        let mut bc = self.c1;
        bc.mul_assign(e, &self.c2);
        let mut s3 = bc;
        s3.double(e);
        let mut s4 = self.c2;
        s4.square(e);

        self.c0 = s3;
        self.c0.mul_by_nonresidue(e);
        self.c0.add_assign(e, &s0);

        self.c1 = s4;
        self.c1.mul_by_nonresidue(e);
        self.c1.add_assign(e, &s1);

        self.c2 = s1;
        self.c2.add_assign(e, &s2);
        self.c2.add_assign(e, &s3);
        self.c2.sub_assign(e, &s0);
        self.c2.sub_assign(e, &s4);
    }

    fn mul_assign(&mut self, e: &Bls381, other: &Self) {
        let mut a_a = self.c0;
        let mut b_b = self.c1;
        let mut c_c = self.c2;
        a_a.mul_assign(e, &other.c0);
        b_b.mul_assign(e, &other.c1);
        c_c.mul_assign(e, &other.c2);

        let mut t1 = other.c1;
        t1.add_assign(e, &other.c2);
        {
            let mut tmp = self.c1;
            tmp.add_assign(e, &self.c2);

            t1.mul_assign(e, &tmp);
            t1.sub_assign(e, &b_b);
            t1.sub_assign(e, &c_c);
            t1.mul_by_nonresidue(e);
            t1.add_assign(e, &a_a);
        }

        let mut t3 = other.c0;
        t3.add_assign(e, &other.c2);
        {
            let mut tmp = self.c0;
            tmp.add_assign(e, &self.c2);

            t3.mul_assign(e, &tmp);
            t3.sub_assign(e, &a_a);
            t3.add_assign(e, &b_b);
            t3.sub_assign(e, &c_c);
        }

        let mut t2 = other.c0;
        t2.add_assign(e, &other.c1);
        {
            let mut tmp = self.c0;
            tmp.add_assign(e, &self.c1);

            t2.mul_assign(e, &tmp);
            t2.sub_assign(e, &a_a);
            t2.sub_assign(e, &b_b);
            c_c.mul_by_nonresidue(e);
            t2.add_assign(e, &c_c);
        }

        self.c0 = t1;
        self.c1 = t2;
        self.c2 = t3;
    }

    fn inverse(&self, e: &Bls381) -> Option<Self> {
        let mut c0 = self.c2;
        c0.mul_by_nonresidue(e);
        c0.mul_assign(e, &self.c1);
        c0.negate(e);
        {
            let mut c0s = self.c0;
            c0s.square(e);
            c0.add_assign(e, &c0s);
        }
        let mut c1 = self.c2;
        c1.square(e);
        c1.mul_by_nonresidue(e);
        {
            let mut c01 = self.c0;
            c01.mul_assign(e, &self.c1);
            c1.sub_assign(e, &c01);
        }
        let mut c2 = self.c1;
        c2.square(e);
        {
            let mut c02 = self.c0;
            c02.mul_assign(e, &self.c2);
            c2.sub_assign(e, &c02);
        }

        let mut tmp1 = self.c2;
        tmp1.mul_assign(e, &c1);
        let mut tmp2 = self.c1;
        tmp2.mul_assign(e, &c2);
        tmp1.add_assign(e, &tmp2);
        tmp1.mul_by_nonresidue(e);
        tmp2 = self.c0;
        tmp2.mul_assign(e, &c0);
        tmp1.add_assign(e, &tmp2);

        match tmp1.inverse(e) {
            Some(t) => {
                let mut tmp = Fq6 {
                    c0: t,
                    c1: t,
                    c2: t
                };
                tmp.c0.mul_assign(e, &c0);
                tmp.c1.mul_assign(e, &c1);
                tmp.c2.mul_assign(e, &c2);

                Some(tmp)
            },
            None => None
        }
    }
}
