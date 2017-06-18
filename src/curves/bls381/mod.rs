use rand;
use std::fmt;

use std::cmp::Ordering;
use std::borrow::Borrow;
use super::{
    Engine,
    Group,
    Curve,
    CurveAffine,
    CurveRepresentation,
    PrimeField,
    PrimeFieldRepr,
    Field,
    SnarkField,
    SqrtField,
    BitIterator,
    Convert,
    Cow,
    multiexp,
    wnaf
};

use serde::ser::{Serialize, Serializer, SerializeTuple};
use serde::de::{Deserialize, Deserializer, Visitor, SeqAccess, Error};

#[macro_use]
mod fp;
#[macro_use]
mod ec;

mod fq2;
mod fq6;
mod fq12;
pub use self::fq2::Fq2;
pub use self::fq6::Fq6;
pub use self::fq12::Fq12;

// The BLS parameter x for BLS12-381 is -0xd201000000010000
const BLS_X: u64 = 0xd201000000010000;
const BLS_X_IS_NEGATIVE: bool = true;

// Multiplicative generator of r-1 order, additionally chosen to be
// nonsquare, so that the root of unity can be used for Tonelli-Shanks
// square root.
const FR_MULTIPLICATIVE_GENERATOR: &'static str = "7";
// Generator taken to the t'th power (r - 1 = 2^s * t with t odd)
const FR_ROOT_OF_UNITY: &'static str = "10238227357739495823651030575849232062558860180284477541189508159991286009131";

// y^2 = x^3 + b
const BLS_B: &'static str = "4";

// Generators for G1 and G2
const BLS_G1_X: &'static str = "3685416753713387016781088315183077757961620795782546409894578378688607592378376318836054947676345821548104185464507";
const BLS_G1_Y: &'static str = "1339506544944476473020471379941921221584933875938349620426543736416511423956333506472724655353366534992391756441569";
const BLS_G2_X_C0: &'static str = "1468726562419257979478817182087966534126060822705880368502120176847060928972041501528146094283660107570228075847785";
const BLS_G2_X_C1: &'static str = "192619896028380442851999297362581720263330513191716562546672373167036922975724849633269992752324699688798815266013";
const BLS_G2_Y_C0: &'static str = "2403786323187906729693550489351819856705060824828191844887396442983655568083290027942568172155055249312505578112188";
const BLS_G2_Y_C1: &'static str = "1887759871634257894151445480492390612163057076015645365125874782999431522408747359398458417857763544644994493115328";

// Implementation of Fq
fp_impl!(
    Fq = (3 mod 4),
    engine = Bls381,
    params = fqparams: FqParams,
    arith = fq_arith,
    repr = FqRepr,
    limbs = 6,
    // q = 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787
    modulus = [ 0xb9feffffffffaaab, 0x1eabfffeb153ffff, 0x6730d2a0f6b0f624, 0x64774b84f38512bf, 0x4b1ba7b6434bacd7, 0x1a0111ea397fe69a ],
    // (2^ 384 ) mod q
    r1 = [ 0x760900000002fffd, 0xebf4000bc40c0002, 0x5f48985753c758ba, 0x77ce585370525745, 0x5c071a97a256ec6d, 0x15f65ec3fa80e493 ],
    // (2^ 384 )^2 mod q
    r2 = [ 0xf4df1f341c341746, 0x0a76e6a609d104f1, 0x8de5476c4c95b6d5, 0x67eb88a9939d83c0, 0x9a793e85b519952d, 0x11988fe592cae3aa ],
    modulus_minus_3_over_4 = [ 0xee7fbfffffffeaaa, 0x07aaffffac54ffff, 0xd9cc34a83dac3d89, 0xd91dd2e13ce144af, 0x92c6e9ed90d2eb35, 0x0680447a8e5ff9a6 ],
    modulus_minus_1_over_2 = [ 0xdcff7fffffffd555, 0x0f55ffff58a9ffff, 0xb39869507b587b12, 0xb23ba5c279c2895f, 0x258dd3db21a5d66b, 0x0d0088f51cbff34d ],
    // - q ^-1 mod 2^64
    inv = 0x89f3fffcfffcfffd
);

// Implementation of Fr
fp_impl!(
    Fr = (1 mod 16),
    engine = Bls381,
    params = frparams: FrParams,
    arith = fr_arith,
    repr = FrRepr,
    limbs = 4,
    // r = 52435875175126190479447740508185965837690552500527637822603658699938581184513
    modulus = [ 0xffffffff00000001, 0x53bda402fffe5bfe, 0x3339d80809a1d805, 0x73eda753299d7d48 ],
    // (2^ 256 ) mod r
    r1 = [ 0x00000001fffffffe, 0x5884b7fa00034802, 0x998c4fefecbc4ff5, 0x1824b159acc5056f ],
    // (2^ 256 )^2 mod r
    r2 = [ 0xc999e990f3f29c6d, 0x2b6cedcb87925c23, 0x05d314967254398f, 0x0748d9d99f59ff11 ],
    modulus_minus_1_over_2 = [ 0x7fffffff80000000, 0xa9ded2017fff2dff, 0x199cec0404d0ec02, 0x39f6d3a994cebea4 ],
    // r - 1 = 2^s * t with t odd
    s = 32 ,
    t = [ 0xfffe5bfeffffffff, 0x09a1d80553bda402, 0x299d7d483339d808, 0x0000000073eda753 ],
    t_plus_1_over_2 = [ 0x7fff2dff80000000, 0x04d0ec02a9ded201, 0x94cebea4199cec04, 0x0000000039f6d3a9 ],
    // - r ^-1 mod 2^64
    inv = 0xfffffffeffffffff
);

impl Group<Bls381> for Fr {
    fn group_zero(_: &Bls381) -> Fr {
        Fr::zero()
    }
    fn group_mul_assign(&mut self, e: &Bls381, scalar: &Fr) {
        self.mul_assign(e, scalar);
    }
    fn group_add_assign(&mut self, e: &Bls381, other: &Self) {
        self.add_assign(e, other);
    }
    fn group_sub_assign(&mut self, e: &Bls381, other: &Self) {
        self.sub_assign(e, other);
    }
}

curve_impl!(Bls381, G1, G1Affine, G1Affine, G1Uncompressed, G1Params, g1params, Fq, Fr);
curve_impl!(Bls381, G2, G2Affine, G2Prepared, G2Uncompressed, G2Params, g2params, Fq2, Fr);

pub struct G1PointData([u8; 96]);
pub struct G2PointData([u8; 192]);

impl Serialize for G1PointData {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: Serializer
    {
        let mut seq = serializer.serialize_tuple(96)?;
        for i in self.0.iter() {
            seq.serialize_element(i)?;
        }
        seq.end()
    }
}

impl<'a> Deserialize<'a> for G1PointData {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where D: Deserializer<'a>
    {
        struct G1PointVisitor;

        impl<'a> Visitor<'a> for G1PointVisitor {
            type Value = G1PointData;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                write!(formatter, "expected 96-byte G1 point X, Y coordinates")
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
                where A: SeqAccess<'a>
            {
                let mut tmp = [0; 96];
                for i in &mut tmp[..] {
                    if let Some(v) = seq.next_element()? {
                        *i = v;
                    } else {
                        return Err(A::Error::custom("not enough bytes"))
                    }
                }

                Ok(G1PointData(tmp))
            }
        }

        deserializer.deserialize_tuple(96, G1PointVisitor)
    }
}

impl Serialize for G2PointData {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: Serializer
    {
        let mut seq = serializer.serialize_tuple(192)?;
        for i in self.0.iter() {
            seq.serialize_element(i)?;
        }
        seq.end()
    }
}

impl<'a> Deserialize<'a> for G2PointData {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where D: Deserializer<'a>
    {
        struct G2PointVisitor;

        impl<'a> Visitor<'a> for G2PointVisitor {
            type Value = G2PointData;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                write!(formatter, "expected 192-byte G2 point X, Y coordinates")
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
                where A: SeqAccess<'a>
            {
                let mut tmp = [0; 192];
                for i in &mut tmp[..] {
                    if let Some(v) = seq.next_element()? {
                        *i = v;
                    } else {
                        return Err(A::Error::custom("not enough bytes"))
                    }
                }

                Ok(G2PointData(tmp))
            }
        }

        deserializer.deserialize_tuple(192, G2PointVisitor)
    }
}

pub enum G1Uncompressed {
    Point(G1PointData),
    Infinity
}
pub enum G2Uncompressed {
    Point(G2PointData),
    Infinity
}

impl Serialize for G1Uncompressed {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: Serializer
    {
        let mut tup = serializer.serialize_tuple(2)?;

        match *self {
            G1Uncompressed::Infinity => {
                tup.serialize_element(&0u8)?;
                tup.serialize_element(&())?;
                tup.end()
            },
            G1Uncompressed::Point(ref v) => {
                tup.serialize_element(&4u8)?;
                tup.serialize_element(v)?;
                tup.end()
            }
        }
    }
}

impl<'a> Deserialize<'a> for G1Uncompressed {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where D: Deserializer<'a>
    {
        use std::fmt;

        struct G1Visitor;

        impl<'a> Visitor<'a> for G1Visitor {
            type Value = G1Uncompressed;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                write!(formatter, "expected uncompressed G1 element")
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
                where A: SeqAccess<'a>
            {
                if let Some(t) = seq.next_element::<u8>()? {
                    if t == 0 {
                        if let Some(()) = seq.next_element::<()>()? {
                            Ok(G1Uncompressed::Infinity)
                        } else {
                            Err(A::Error::custom("expected null coordinate"))
                        }
                    } else if t == 4 {
                        if let Some(p) = seq.next_element::<G1PointData>()? {
                            Ok(G1Uncompressed::Point(p))
                        } else {
                            Err(A::Error::custom("expected X, Y coordinate"))
                        }
                    } else {
                        Err(A::Error::custom("expected IEEE prefix for uncompressed G1 element"))
                    }
                } else {
                    Err(A::Error::custom("expected IEEE prefix for uncompressed G1 element"))
                }
            }
        }

        let v = G1Visitor;

        deserializer.deserialize_tuple(2, v)
    }
}

impl Serialize for G2Uncompressed {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: Serializer
    {
        let mut tup = serializer.serialize_tuple(2)?;

        match *self {
            G2Uncompressed::Infinity => {
                tup.serialize_element(&0u8)?;
                tup.serialize_element(&())?;
                tup.end()
            },
            G2Uncompressed::Point(ref v) => {
                tup.serialize_element(&4u8)?;
                tup.serialize_element(v)?;
                tup.end()
            }
        }
    }
}

impl<'a> Deserialize<'a> for G2Uncompressed {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where D: Deserializer<'a>
    {
        use std::fmt;

        struct G2Visitor;

        impl<'a> Visitor<'a> for G2Visitor {
            type Value = G2Uncompressed;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                write!(formatter, "expected uncompressed G2 element")
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
                where A: SeqAccess<'a>
            {
                if let Some(t) = seq.next_element::<u8>()? {
                    if t == 0 {
                        if let Some(()) = seq.next_element::<()>()? {
                            Ok(G2Uncompressed::Infinity)
                        } else {
                            Err(A::Error::custom("expected null coordinate"))
                        }
                    } else if t == 4 {
                        if let Some(p) = seq.next_element::<G2PointData>()? {
                            Ok(G2Uncompressed::Point(p))
                        } else {
                            Err(A::Error::custom("expected X, Y coordinate"))
                        }
                    } else {
                        Err(A::Error::custom("expected IEEE prefix for uncompressed G2 element"))
                    }
                } else {
                    Err(A::Error::custom("expected IEEE prefix for uncompressed G2 element"))
                }
            }
        }

        let v = G2Visitor;

        deserializer.deserialize_tuple(2, v)
    }
}

impl CurveRepresentation<Bls381> for G1Uncompressed {
    type Affine = G1Affine;

    fn to_affine_unchecked(&self, e: &Bls381) -> Result<G1Affine, ()> {
        match self {
            &G1Uncompressed::Infinity => {
                Ok(G1::zero(e).to_affine(e))
            },
            &G1Uncompressed::Point(ref bytes) => {
                use byteorder::{ReadBytesExt, BigEndian};

                let mut bytes = &bytes.0[..];

                let mut x = [0; 6];
                let mut y = [0; 6];

                for x in x.iter_mut().rev() {
                    *x = bytes.read_u64::<BigEndian>().unwrap();
                }
                for y in y.iter_mut().rev() {
                    *y = bytes.read_u64::<BigEndian>().unwrap();
                }

                Ok(G1Affine {
                    x: try!(Fq::from_repr(e, FqRepr(x))),
                    y: try!(Fq::from_repr(e, FqRepr(y))),
                    infinity: false
                })
            }
        }
    }
}

impl CurveRepresentation<Bls381> for G2Uncompressed {
    type Affine = G2Affine;

    fn to_affine_unchecked(&self, e: &Bls381) -> Result<G2Affine, ()> {
        match self {
            &G2Uncompressed::Infinity => {
                Ok(G2::zero(e).to_affine(e))
            },
            &G2Uncompressed::Point(ref bytes) => {
                use byteorder::{ReadBytesExt, BigEndian};

                let mut bytes = &bytes.0[..];

                let mut x = [0; 12];
                let mut y = [0; 12];

                for x in x.iter_mut().rev() {
                    *x = bytes.read_u64::<BigEndian>().unwrap();
                }
                for y in y.iter_mut().rev() {
                    *y = bytes.read_u64::<BigEndian>().unwrap();
                }

                if let (Some(x_c1), x_c0) = fq_arith::divrem(&x, &e.fqparams.modulus) {
                    if let (Some(y_c1), y_c0) = fq_arith::divrem(&y, &e.fqparams.modulus) {
                        return Ok(G2Affine {
                            x: Fq2 {
                                c0: try!(Fq::from_repr(e, FqRepr(x_c0))),
                                c1: try!(Fq::from_repr(e, FqRepr(x_c1)))
                            },
                            y: Fq2 {
                                c0: try!(Fq::from_repr(e, FqRepr(y_c0))),
                                c1: try!(Fq::from_repr(e, FqRepr(y_c1)))
                            },
                            infinity: false
                        });
                    }
                }

                Err(())
            }
        }
    }
}

impl G1Uncompressed {
    fn from_affine(p: &G1Affine, e: &Bls381) -> Self {
        if p.infinity {
            G1Uncompressed::Infinity
        } else {
            use byteorder::{WriteBytesExt, BigEndian};

            let mut tmp = [0; 96];

            {
                let mut tmp = &mut tmp[0..];
                for &digit in p.x.into_repr(e).0.iter().rev() {
                    tmp.write_u64::<BigEndian>(digit).unwrap();
                }
            }

            {
                let mut tmp = &mut tmp[48..];
                for &digit in p.y.into_repr(e).0.iter().rev() {
                    tmp.write_u64::<BigEndian>(digit).unwrap();
                }
            }

            G1Uncompressed::Point(G1PointData(tmp))
        }
    }
}

impl G2Uncompressed {
    fn from_affine(p: &G2Affine, e: &Bls381) -> Self {
        if p.infinity {
            G2Uncompressed::Infinity
        } else {
            use byteorder::{WriteBytesExt, BigEndian};

            let mut tmp = [0; 192];

            {
                let mut tmp = &mut tmp[0..];
                let mut x = [0; 12];
                fq_arith::mac3(&mut x, &p.x.c1.into_repr(e).0, &e.fqparams.modulus);
                fq_arith::add_carry(&mut x, &p.x.c0.into_repr(e).0);

                for &digit in x.iter().rev() {
                    tmp.write_u64::<BigEndian>(digit).unwrap();
                }
            }

            {
                let mut tmp = &mut tmp[96..];
                let mut y = [0; 12];
                fq_arith::mac3(&mut y, &p.y.c1.into_repr(e).0, &e.fqparams.modulus);
                fq_arith::add_carry(&mut y, &p.y.c0.into_repr(e).0);

                for &digit in y.iter().rev() {
                    tmp.write_u64::<BigEndian>(digit).unwrap();
                }
            }

            G2Uncompressed::Point(G2PointData(tmp))
        }
    }
}

impl G1Affine {
    fn from_engine(_: &Bls381, p: G1Affine) -> Self {
        p
    }
}

#[derive(Clone)]
pub struct G2Prepared {
    coeffs: Vec<(Fq2, Fq2, Fq2)>,
    infinity: bool
}

impl G2Prepared {
    fn is_zero(&self) -> bool {
        self.infinity
    }

    fn from_engine(e: &Bls381, q: G2Affine) -> Self {
        if q.is_zero() {
            return G2Prepared {
                coeffs: vec![],
                infinity: true
            }
        }

        fn doubling_step(
            e: &Bls381,
            r: &mut G2
        ) -> (Fq2, Fq2, Fq2)
        {
            // Adaptation of Algorithm 26, https://eprint.iacr.org/2010/354.pdf
            let mut tmp0 = r.x;
            tmp0.square(e);

            let mut tmp1 = r.y;
            tmp1.square(e);

            let mut tmp2 = tmp1;
            tmp2.square(e);

            let mut tmp3 = tmp1;
            tmp3.add_assign(e, &r.x);
            tmp3.square(e);
            tmp3.sub_assign(e, &tmp0);
            tmp3.sub_assign(e, &tmp2);
            tmp3.double(e);

            let mut tmp4 = tmp0;
            tmp4.double(e);
            tmp4.add_assign(e, &tmp0);

            let mut tmp6 = r.x;
            tmp6.add_assign(e, &tmp4);

            let mut tmp5 = tmp4;
            tmp5.square(e);

            let mut zsquared = r.z;
            zsquared.square(e);

            r.x = tmp5;
            r.x.sub_assign(e, &tmp3);
            r.x.sub_assign(e, &tmp3);

            r.z.add_assign(e, &r.y);
            r.z.square(e);
            r.z.sub_assign(e, &tmp1);
            r.z.sub_assign(e, &zsquared);

            r.y = tmp3;
            r.y.sub_assign(e, &r.x);
            r.y.mul_assign(e, &tmp4);
            
            tmp2.double(e);
            tmp2.double(e);
            tmp2.double(e);

            r.y.sub_assign(e, &tmp2);

            tmp3 = tmp4;
            tmp3.mul_assign(e, &zsquared);
            tmp3.double(e);
            tmp3.negate(e);

            tmp6.square(e);
            tmp6.sub_assign(e, &tmp0);
            tmp6.sub_assign(e, &tmp5);

            tmp1.double(e);
            tmp1.double(e);

            tmp6.sub_assign(e, &tmp1);

            tmp0 = r.z;
            tmp0.mul_assign(e, &zsquared);
            tmp0.double(e);

            (tmp0, tmp3, tmp6)
        }

        fn addition_step(
            e: &Bls381,
            r: &mut G2,
            q: &G2Affine
        ) -> (Fq2, Fq2, Fq2)
        {
            // Adaptation of Algorithm 27, https://eprint.iacr.org/2010/354.pdf
            let mut zsquared = r.z;
            zsquared.square(e);

            let mut ysquared = q.y;
            ysquared.square(e);

            let mut t0 = zsquared;
            t0.mul_assign(e, &q.x);

            let mut t1 = q.y;
            t1.add_assign(e, &r.z);
            t1.square(e);
            t1.sub_assign(e, &ysquared);
            t1.sub_assign(e, &zsquared);
            t1.mul_assign(e, &zsquared);

            let mut t2 = t0;
            t2.sub_assign(e, &r.x);

            let mut t3 = t2;
            t3.square(e);

            let mut t4 = t3;
            t4.double(e);
            t4.double(e);

            let mut t5 = t4;
            t5.mul_assign(e, &t2);

            let mut t6 = t1;
            t6.sub_assign(e, &r.y);
            t6.sub_assign(e, &r.y);

            let mut t9 = t6;
            t9.mul_assign(e, &q.x);

            let mut t7 = t4;
            t7.mul_assign(e, &r.x);

            r.x = t6;
            r.x.square(e);
            r.x.sub_assign(e, &t5);
            r.x.sub_assign(e, &t7);
            r.x.sub_assign(e, &t7);

            r.z.add_assign(e, &t2);
            r.z.square(e);
            r.z.sub_assign(e, &zsquared);
            r.z.sub_assign(e, &t3);

            let mut t10 = q.y;
            t10.add_assign(e, &r.z);

            let mut t8 = t7;
            t8.sub_assign(e, &r.x);
            t8.mul_assign(e, &t6);

            t0 = r.y;
            t0.mul_assign(e, &t5);
            t0.double(e);

            r.y = t8;
            r.y.sub_assign(e, &t0);

            t10.square(e);
            t10.sub_assign(e, &ysquared);

            let mut ztsquared = r.z;
            ztsquared.square(e);

            t10.sub_assign(e, &ztsquared);

            t9.double(e);
            t9.sub_assign(e, &t10);

            t10 = r.z;
            t10.double(e);
            
            t6.negate(e);

            t1 = t6;
            t1.double(e);

            (t10, t1, t9)
        }

        let mut coeffs = vec![];
        let mut r = q.to_jacobian(e);

        let mut found_one = false;
        for i in BitIterator::new(&[BLS_X >> 1]) {
            if !found_one {
                found_one = i;
                continue;
            }

            coeffs.push(doubling_step(e, &mut r));

            if i {
                coeffs.push(addition_step(e, &mut r, &q));
            }
        }

        coeffs.push(doubling_step(e, &mut r));

        G2Prepared {
            coeffs: coeffs,
            infinity: false
        }
    }
}

#[derive(Clone)]
pub struct Bls381 {
    fqparams: FqParams,
    frparams: FrParams,
    g1params: G1Params,
    g2params: G2Params,
    frobenius_coeff_fq2: [Fq; 2],
    frobenius_coeff_fq6_c1: [Fq2; 6],
    frobenius_coeff_fq6_c2: [Fq2; 6],
    frobenius_coeff_fq12: [Fq2; 12]
}

thread_local!(static ENGINE: Bls381 = Bls381::new());

impl SnarkField<Bls381> for Fr {
    fn s(e: &Bls381) -> u64 {
        e.frparams.s
    }
    fn multiplicative_generator(e: &Bls381) -> Self {
        e.frparams.multiplicative_generator
    }
    fn root_of_unity(e: &Bls381) -> Self {
        e.frparams.root_of_unity
    }
}

impl Engine for Bls381 {
    type Fq = Fq;
    type Fr = Fr;
    type Fqe = Fq2;
    type Fqk = Fq12;

    type G1 = G1;
    type G2 = G2;

    fn with<R, F: for<'a> FnOnce(&'a Self) -> R>(cb: F) -> R {
        ENGINE.with(|e| {
            cb(e)
        })
    }

    fn new() -> Bls381 {
        let mut tmp = Bls381 {
            fqparams: FqParams::partial_init(),
            frparams: FrParams::partial_init(),
            g1params: G1Params {
                zero: G1 { x: Fq::zero(), y: Fq::zero(), z: Fq::zero() },
                one: G1 { x: Fq::zero(), y: Fq::zero(), z: Fq::zero() },
                coeff_b: Fq::zero(),
                windows: vec![11, 35, 110],
                batch_windows: (4, vec![2, 3, 10, 20, 53, 111, 266, 426, 1273, 4742, 6054, 6054, 6054])
            },
            g2params: G2Params {
                zero: G2 { x: Fq2::zero(), y: Fq2::zero(), z: Fq2::zero() },
                one: G2 { x: Fq2::zero(), y: Fq2::zero(), z: Fq2::zero() },
                coeff_b: Fq2::zero(),
                windows: vec![11, 35, 114],
                batch_windows: (4, vec![2, 4, 10, 29, 54, 120, 314, 314, 314, 314])
            },
            frobenius_coeff_fq2: [Fq::zero(); 2],
            frobenius_coeff_fq6_c1: [Fq2::zero(); 6],
            frobenius_coeff_fq6_c2: [Fq2::zero(); 6],
            frobenius_coeff_fq12: [Fq2::zero(); 12]
        };

        // Initialize the base 10 numbers for from_str
        tmp.fqparams.base10 = FqParams::base10(&tmp);
        tmp.frparams.base10 = FrParams::base10(&tmp);

        // Initialize field parameters
        tmp.frparams.multiplicative_generator = Fr::from_str(&tmp, FR_MULTIPLICATIVE_GENERATOR).unwrap();
        tmp.frparams.root_of_unity = Fr::from_str(&tmp, FR_ROOT_OF_UNITY).unwrap();

        tmp.fqparams.num_bits = 381;
        tmp.frparams.num_bits = 255;

        // Initialize the coefficients for the Frobenius map
        tmp.frobenius_coeff_fq2[0] = Fq::from_str(&tmp, "1").unwrap();
        tmp.frobenius_coeff_fq2[1] = Fq::from_str(&tmp, "4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559786").unwrap();
        tmp.frobenius_coeff_fq6_c1[0] = Fq2 {
            c0: Fq::from_str(&tmp, "1").unwrap(),
            c1: Fq::from_str(&tmp, "0").unwrap()
        };
        tmp.frobenius_coeff_fq6_c1[1] = Fq2 {
            c0: Fq::from_str(&tmp, "0").unwrap(),
            c1: Fq::from_str(&tmp, "4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436").unwrap()
        };
        tmp.frobenius_coeff_fq6_c1[2] = Fq2 {
            c0: Fq::from_str(&tmp, "793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620350").unwrap(),
            c1: Fq::from_str(&tmp, "0").unwrap()
        };
        tmp.frobenius_coeff_fq6_c1[3] = Fq2 {
            c0: Fq::from_str(&tmp, "0").unwrap(),
            c1: Fq::from_str(&tmp, "1").unwrap()
        };
        tmp.frobenius_coeff_fq6_c1[4] = Fq2 {
            c0: Fq::from_str(&tmp, "4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436").unwrap(),
            c1: Fq::from_str(&tmp, "0").unwrap()
        };
        tmp.frobenius_coeff_fq6_c1[5] = Fq2 {
            c0: Fq::from_str(&tmp, "0").unwrap(),
            c1: Fq::from_str(&tmp, "793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620350").unwrap()
        };
        tmp.frobenius_coeff_fq6_c2[0] = Fq2 {
            c0: Fq::from_str(&tmp, "1").unwrap(),
            c1: Fq::from_str(&tmp, "0").unwrap()
        };
        tmp.frobenius_coeff_fq6_c2[1] = Fq2 {
            c0: Fq::from_str(&tmp, "4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939437").unwrap(),
            c1: Fq::from_str(&tmp, "0").unwrap()
        };
        tmp.frobenius_coeff_fq6_c2[2] = Fq2 {
            c0: Fq::from_str(&tmp, "4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436").unwrap(),
            c1: Fq::from_str(&tmp, "0").unwrap()
        };
        tmp.frobenius_coeff_fq6_c2[3] = Fq2 {
            c0: Fq::from_str(&tmp, "4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559786").unwrap(),
            c1: Fq::from_str(&tmp, "0").unwrap()
        };
        tmp.frobenius_coeff_fq6_c2[4] = Fq2 {
            c0: Fq::from_str(&tmp, "793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620350").unwrap(),
            c1: Fq::from_str(&tmp, "0").unwrap()
        };
        tmp.frobenius_coeff_fq6_c2[5] = Fq2 {
            c0: Fq::from_str(&tmp, "793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620351").unwrap(),
            c1: Fq::from_str(&tmp, "0").unwrap()
        };
        tmp.frobenius_coeff_fq12[0] = Fq2 {
            c0: Fq::from_str(&tmp, "1").unwrap(),
            c1: Fq::from_str(&tmp, "0").unwrap()
        };
        tmp.frobenius_coeff_fq12[1] = Fq2 {
            c0: Fq::from_str(&tmp, "3850754370037169011952147076051364057158807420970682438676050522613628423219637725072182697113062777891589506424760").unwrap(),
            c1: Fq::from_str(&tmp, "151655185184498381465642749684540099398075398968325446656007613510403227271200139370504932015952886146304766135027").unwrap()
        };
        tmp.frobenius_coeff_fq12[2] = Fq2 {
            c0: Fq::from_str(&tmp, "793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620351").unwrap(),
            c1: Fq::from_str(&tmp, "0").unwrap()
        };
        tmp.frobenius_coeff_fq12[3] = Fq2 {
            c0: Fq::from_str(&tmp, "2973677408986561043442465346520108879172042883009249989176415018091420807192182638567116318576472649347015917690530").unwrap(),
            c1: Fq::from_str(&tmp, "1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257").unwrap()
        };
        tmp.frobenius_coeff_fq12[4] = Fq2 {
            c0: Fq::from_str(&tmp, "793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620350").unwrap(),
            c1: Fq::from_str(&tmp, "0").unwrap()
        };
        tmp.frobenius_coeff_fq12[5] = Fq2 {
            c0: Fq::from_str(&tmp, "3125332594171059424908108096204648978570118281977575435832422631601824034463382777937621250592425535493320683825557").unwrap(),
            c1: Fq::from_str(&tmp, "877076961050607968509681729531255177986764537961432449499635504522207616027455086505066378536590128544573588734230").unwrap()
        };
        tmp.frobenius_coeff_fq12[6] = Fq2 {
            c0: Fq::from_str(&tmp, "4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559786").unwrap(),
            c1: Fq::from_str(&tmp, "0").unwrap()
        };
        tmp.frobenius_coeff_fq12[7] = Fq2 {
            c0: Fq::from_str(&tmp, "151655185184498381465642749684540099398075398968325446656007613510403227271200139370504932015952886146304766135027").unwrap(),
            c1: Fq::from_str(&tmp, "3850754370037169011952147076051364057158807420970682438676050522613628423219637725072182697113062777891589506424760").unwrap()
        };
        tmp.frobenius_coeff_fq12[8] = Fq2 {
            c0: Fq::from_str(&tmp, "4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436").unwrap(),
            c1: Fq::from_str(&tmp, "0").unwrap()
        };
        tmp.frobenius_coeff_fq12[9] = Fq2 {
            c0: Fq::from_str(&tmp, "1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257").unwrap(),
            c1: Fq::from_str(&tmp, "2973677408986561043442465346520108879172042883009249989176415018091420807192182638567116318576472649347015917690530").unwrap()
        };
        tmp.frobenius_coeff_fq12[10] = Fq2 {
            c0: Fq::from_str(&tmp, "4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939437").unwrap(),
            c1: Fq::from_str(&tmp, "0").unwrap()
        };
        tmp.frobenius_coeff_fq12[11] = Fq2 {
            c0: Fq::from_str(&tmp, "877076961050607968509681729531255177986764537961432449499635504522207616027455086505066378536590128544573588734230").unwrap(),
            c1: Fq::from_str(&tmp, "3125332594171059424908108096204648978570118281977575435832422631601824034463382777937621250592425535493320683825557").unwrap()
        };

        // G1 parameters
        tmp.g1params.zero.y = Fq::one(&tmp);
        tmp.g1params.coeff_b = Fq::from_str(&tmp, BLS_B).unwrap();
        tmp.g1params.one.x = Fq::from_str(&tmp, BLS_G1_X).unwrap();
        tmp.g1params.one.y = Fq::from_str(&tmp, BLS_G1_Y).unwrap();
        tmp.g1params.one.z = Fq::one(&tmp);

        // G2 parameters
        tmp.g2params.zero.y = Fq2::one(&tmp);
        tmp.g2params.coeff_b = Fq2 {
            c0: Fq::from_str(&tmp, BLS_B).unwrap(),
            c1: Fq::from_str(&tmp, BLS_B).unwrap()
        };
        tmp.g2params.one.x = Fq2 {
            c0: Fq::from_str(&tmp, BLS_G2_X_C0).unwrap(),
            c1: Fq::from_str(&tmp, BLS_G2_X_C1).unwrap()
        };
        tmp.g2params.one.y = Fq2 {
            c0: Fq::from_str(&tmp, BLS_G2_Y_C0).unwrap(),
            c1: Fq::from_str(&tmp, BLS_G2_Y_C1).unwrap()
        };
        tmp.g2params.one.z = Fq2::one(&tmp);

        tmp
    }

    fn final_exponentiation(&self, r: &Fq12) -> Fq12 {
        let mut f1 = *r;
        f1.unitary_inverse(self);
        let mut f2 = r.inverse(self).unwrap();
        let mut r = f1;
        r.mul_assign(self, &f2);
        f2 = r;
        r.frobenius_map(self, 2);
        r.mul_assign(self, &f2);

        fn exp_by_x(e: &Bls381, f: &mut Fq12, x: u64)
        {
            *f = f.pow(e, &[x]);
            if BLS_X_IS_NEGATIVE {
                f.unitary_inverse(e);
            }
        }
        
        let mut x = BLS_X;
        let mut y0 = r;
        y0.square(self);
        let mut y1 = y0;
        exp_by_x(self, &mut y1, x);
        x >>= 1;
        let mut y2 = y1;
        exp_by_x(self, &mut y2, x);
        x <<= 1;
        let mut y3 = r;
        y3.unitary_inverse(self);
        y1.mul_assign(self, &y3);
        y1.unitary_inverse(self);
        y1.mul_assign(self, &y2);
        y2 = y1;
        exp_by_x(self, &mut y2, x);
        y3 = y2;
        exp_by_x(self, &mut y3, x);
        y1.unitary_inverse(self);
        y3.mul_assign(self, &y1);
        y1.unitary_inverse(self);
        y1.frobenius_map(self, 3);
        y2.frobenius_map(self, 2);
        y1.mul_assign(self, &y2);
        y2 = y3;
        exp_by_x(self, &mut y2, x);
        y2.mul_assign(self, &y0);
        y2.mul_assign(self, &r);
        y1.mul_assign(self, &y2);
        y2 = y3;
        y2.frobenius_map(self, 1);
        y1.mul_assign(self, &y2);
        y1
    }

    fn miller_loop<'a, I>(&self, i: I) -> Self::Fqk
        where I: IntoIterator<Item=&'a (
                                    &'a <Self::G1 as Curve<Self>>::Prepared,
                                    &'a <Self::G2 as Curve<Self>>::Prepared
                               )>
    {
        let mut pairs = vec![];
        for &(p, q) in i {
            if !p.is_zero() && !q.is_zero() {
                pairs.push((p, q.coeffs.iter()));
            }
        }

        // Twisting isomorphism from E to E'
        fn ell(
            e: &Bls381,
            f: &mut Fq12,
            coeffs: &(Fq2, Fq2, Fq2),
            p: &G1Affine
        )
        {
            let mut c0 = coeffs.0;
            let mut c1 = coeffs.1;

            c0.c0.mul_assign(e, &p.y);
            c0.c1.mul_assign(e, &p.y);

            c1.c0.mul_assign(e, &p.x);
            c1.c1.mul_assign(e, &p.x);

            // Sparse multiplication in Fq12
            f.mul_by_015(e, &coeffs.2, &c1, &c0);
        }

        let mut f = Fq12::one(self);

        let mut found_one = false;
        for i in BitIterator::new(&[BLS_X >> 1]) {
            if !found_one {
                found_one = i;
                continue;
            }

            for &mut (p, ref mut coeffs) in &mut pairs {
                ell(self, &mut f, coeffs.next().unwrap(), p);
            }

            if i {
                for &mut (p, ref mut coeffs) in &mut pairs {
                    ell(self, &mut f, coeffs.next().unwrap(), p);
                }
            }

            f.square(self);
        }

        for &mut (p, ref mut coeffs) in &mut pairs {
            ell(self, &mut f, coeffs.next().unwrap(), p);
        }

        f
    }

    fn batchexp<G: Curve<Self>, S: AsRef<[Self::Fr]>>(&self, g: &mut [G::Affine], scalars: S, coeff: Option<&Self::Fr>)
    {
        use crossbeam;
        use num_cpus;

        assert_eq!(g.len(), scalars.as_ref().len());

        let chunk = (g.len() / num_cpus::get()) + 1;

        crossbeam::scope(|scope| {
            for (g, s) in g.chunks_mut(chunk).zip(scalars.as_ref().chunks(chunk)) {
                scope.spawn(move || {
                    let mut table = wnaf::WindowTable::new(self, G::zero(self), 2);
                    let mut scratch = wnaf::WNAFTable::new();

                    for (g, s) in g.iter_mut().zip(s.iter()) {
                        let mut s = *s;
                        match coeff {
                            Some(coeff) => {
                                s.mul_assign(self, coeff);
                            },
                            _ => {}
                        };
                        *g = g.to_jacobian(self)
                              .optimal_exp(self, s.into_repr(self), &mut table, &mut scratch)
                              .to_affine(self);
                    }
                });
            }
        });
    }

    fn batch_baseexp<G: Curve<Self>, S: AsRef<[Self::Fr]>>(&self, table: &wnaf::WindowTable<Self, G>, s: S) -> Vec<G::Affine>
    {
        use crossbeam;
        use num_cpus;

        let s = s.as_ref();
        let mut ret = vec![G::zero(self).to_affine(self); s.len()];

        crossbeam::scope(|scope| {
            let chunk = (s.len() / num_cpus::get()) + 1;

            for (s, b) in s.chunks(chunk).zip(ret.chunks_mut(chunk)) {
                scope.spawn(move || {
                    let mut scratch = wnaf::WNAFTable::new();

                    for (s, b) in s.iter().zip(b.iter_mut()) {
                        scratch.set_scalar(table, s.into_repr(self));
                        *b = table.exp(self, &scratch).to_affine(self);
                    }
                });
            }
        });

        ret
    }

    fn multiexp<G: Curve<Self>>(&self, g: &[G::Affine], s: &[Fr]) -> Result<G, ()> {
        super::multiexp::perform_multiexp(self, g, s)
    }
}

#[cfg(test)]
mod tests;
