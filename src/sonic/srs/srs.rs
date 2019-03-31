use crate::pairing::ff::{Field, PrimeField};
use crate::pairing::{CurveAffine, CurveProjective, Engine, Wnaf};

use std::io::{self, Read, Write};
use std::sync::Arc;
use byteorder::{BigEndian, WriteBytesExt, ReadBytesExt};

#[derive(Clone, Eq)]
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

impl<E: Engine> PartialEq for SRS<E> {
    fn eq(&self, other: &SRS<E>) -> bool {
        self.d == other.d &&
        self.g_negative_x == other.g_negative_x &&
        self.g_positive_x == other.g_positive_x &&
        self.h_negative_x == other.h_negative_x &&
        self.h_positive_x == other.h_positive_x &&
        self.g_negative_x_alpha == other.g_negative_x_alpha &&
        self.g_positive_x_alpha == other.g_positive_x_alpha &&
        self.h_negative_x_alpha == other.h_negative_x_alpha &&
        self.h_positive_x_alpha == other.h_positive_x_alpha
    }
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

impl<E: Engine> SRS<E> {
    pub fn write<W: Write>(
        &self,
        mut writer: W
    ) -> io::Result<()>
    {
        assert_eq!(self.d + 1, self.g_negative_x.len());
        assert_eq!(self.d + 1, self.g_positive_x.len());

        assert_eq!(self.d + 1, self.h_negative_x.len());
        assert_eq!(self.d + 1, self.h_positive_x.len());

        assert_eq!(self.d, self.g_negative_x_alpha.len());
        assert_eq!(self.d, self.g_positive_x_alpha.len());

        assert_eq!(self.d + 1, self.h_negative_x_alpha.len());
        assert_eq!(self.d + 1, self.h_positive_x_alpha.len());

        writer.write_u32::<BigEndian>(self.d as u32)?;

        for g in &self.g_negative_x[..] {
            writer.write_all(g.into_uncompressed().as_ref())?;
        }
        for g in &self.g_positive_x[..] {
            writer.write_all(g.into_uncompressed().as_ref())?;
        }

        for g in &self.h_negative_x[..] {
            writer.write_all(g.into_uncompressed().as_ref())?;
        }
        for g in &self.h_positive_x[..] {
            writer.write_all(g.into_uncompressed().as_ref())?;
        }

        for g in &self.g_negative_x_alpha[..] {
            writer.write_all(g.into_uncompressed().as_ref())?;
        }
        for g in &self.g_positive_x_alpha[..] {
            writer.write_all(g.into_uncompressed().as_ref())?;
        }

        for g in &self.h_negative_x_alpha[..] {
            writer.write_all(g.into_uncompressed().as_ref())?;
        }
        for g in &self.h_positive_x_alpha[..] {
            writer.write_all(g.into_uncompressed().as_ref())?;
        }

        Ok(())
    }

    pub fn read<R: Read>(
        mut reader: R,
        checked: bool
    ) -> io::Result<Self>
    {
        use crate::pairing::EncodedPoint;

        let read_g1 = |reader: &mut R| -> io::Result<E::G1Affine> {
            let mut repr = <E::G1Affine as CurveAffine>::Uncompressed::empty();
            reader.read_exact(repr.as_mut())?;

            if checked {
                repr
                .into_affine()
            } else {
                repr
                .into_affine_unchecked()
            }
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
            .and_then(|e| if e.is_zero() {
                Err(io::Error::new(io::ErrorKind::InvalidData, "point at infinity"))
            } else {
                Ok(e)
            })
        };

        let read_g2 = |reader: &mut R| -> io::Result<E::G2Affine> {
            let mut repr = <E::G2Affine as CurveAffine>::Uncompressed::empty();
            reader.read_exact(repr.as_mut())?;

            if checked {
                repr
                .into_affine()
            } else {
                repr
                .into_affine_unchecked()
            }
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
            .and_then(|e| if e.is_zero() {
                Err(io::Error::new(io::ErrorKind::InvalidData, "point at infinity"))
            } else {
                Ok(e)
            })
        };

        let mut g_negative_x = vec![];
        let mut g_positive_x = vec![];

        let mut h_negative_x = vec![];
        let mut h_positive_x = vec![];

        let mut g_negative_x_alpha = vec![];
        let mut g_positive_x_alpha = vec![];

        let mut h_negative_x_alpha = vec![];
        let mut h_positive_x_alpha = vec![];

        let d = reader.read_u32::<BigEndian>()? as usize;

        {
            for _ in 0..(d+1) {
                g_negative_x.push(read_g1(&mut reader)?);
            }
            for _ in 0..(d+1) {
                g_positive_x.push(read_g1(&mut reader)?);
            }
        }
        
        {
            for _ in 0..(d+1) {
                h_negative_x.push(read_g2(&mut reader)?);
            }
            for _ in 0..(d+1) {
                h_positive_x.push(read_g2(&mut reader)?);
            }
        }

        {
            for _ in 0..d {
                g_negative_x_alpha.push(read_g1(&mut reader)?);
            }
            for _ in 0..d {
                g_positive_x_alpha.push(read_g1(&mut reader)?);
            }
        }

        {
            for _ in 0..(d+1) {
                h_negative_x_alpha.push(read_g2(&mut reader)?);
            }
            for _ in 0..(d+1) {
                h_positive_x_alpha.push(read_g2(&mut reader)?);
            }
        }
        
        Ok(Self {
            d: d,
            g_negative_x: g_negative_x,
            g_positive_x: g_positive_x,
            h_negative_x: h_negative_x,
            h_positive_x: h_positive_x,
            g_negative_x_alpha: g_negative_x_alpha,
            g_positive_x_alpha: g_positive_x_alpha,
            h_negative_x_alpha: h_negative_x_alpha,
            h_positive_x_alpha: h_positive_x_alpha
        })
    }
}