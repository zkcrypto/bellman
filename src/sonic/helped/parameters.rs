use ff::{
    Field,
    PrimeField, 
    PrimeFieldRepr
};

use pairing::{
    Engine,
    CurveAffine,
    EncodedPoint
};

use ::{
    SynthesisError
};

use multiexp::SourceBuilder;
use std::io::{self, Read, Write};
use std::sync::Arc;
use byteorder::{BigEndian, WriteBytesExt, ReadBytesExt};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SxyAdvice<E: Engine> {
    pub s: E::G1Affine,
    pub opening: E::G1Affine,
    pub szy: E::Fr,
}


#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof<E: Engine> {
    pub r: E::G1Affine,
    pub t: E::G1Affine,
    pub rz: E::Fr,
    pub rzy: E::Fr,
    pub z_opening: E::G1Affine,
    pub zy_opening: E::G1Affine
}

impl<E: Engine> Proof<E> {
    pub fn write<W: Write>(
        &self,
        mut writer: W
    ) -> io::Result<()>
    {
        use ff::{PrimeField, PrimeFieldRepr};
        writer.write_all(self.r.into_compressed().as_ref())?;
        writer.write_all(self.t.into_compressed().as_ref())?;
        let mut buffer = vec![];
        self.rz.into_repr().write_be(&mut buffer)?;
        writer.write_all(&buffer[..])?;
        self.rzy.into_repr().write_be(&mut buffer)?;
        writer.write_all(&buffer[..])?;
        writer.write_all(self.z_opening.into_compressed().as_ref())?;
        writer.write_all(self.zy_opening.into_compressed().as_ref())?;

        Ok(())
    }

    pub fn read<R: Read>(
        mut reader: R
    ) -> io::Result<Self>
    {
        let mut g1_repr = <E::G1Affine as CurveAffine>::Compressed::empty();
        let mut fr_repr = E::Fr::zero().into_repr();

        reader.read_exact(g1_repr.as_mut())?;
        let r = g1_repr
                .into_affine()
                .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
                .and_then(|e| if e.is_zero() {
                    Err(io::Error::new(io::ErrorKind::InvalidData, "point at infinity"))
                } else {
                    Ok(e)
                })?;

        reader.read_exact(g1_repr.as_mut())?;
        let t = g1_repr
                .into_affine()
                .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
                .and_then(|e| if e.is_zero() {
                    Err(io::Error::new(io::ErrorKind::InvalidData, "point at infinity"))
                } else {
                    Ok(e)
                })?;

        fr_repr.read_be(&mut reader)?;
        let rz = E::Fr::from_repr(fr_repr)
                .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
                .and_then(|e| if e.is_zero() {
                    Err(io::Error::new(io::ErrorKind::InvalidData, "field element is zero"))
                } else {
                    Ok(e)
                })?;

        fr_repr.read_be(&mut reader)?;
        let rzy = E::Fr::from_repr(fr_repr)
                .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
                .and_then(|e| if e.is_zero() {
                    Err(io::Error::new(io::ErrorKind::InvalidData, "field element is zero"))
                } else {
                    Ok(e)
                })?;

        
        reader.read_exact(g1_repr.as_mut())?;
        let z_opening = g1_repr
                .into_affine()
                .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
                .and_then(|e| if e.is_zero() {
                    Err(io::Error::new(io::ErrorKind::InvalidData, "point at infinity"))
                } else {
                    Ok(e)
                })?;

        reader.read_exact(g1_repr.as_mut())?;
        let zy_opening = g1_repr
                .into_affine()
                .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
                .and_then(|e| if e.is_zero() {
                    Err(io::Error::new(io::ErrorKind::InvalidData, "point at infinity"))
                } else {
                    Ok(e)
                })?;

        Ok(Proof {
            r: r,
            t: t,
            rz: rz,
            rzy: rzy,
            z_opening: z_opening,
            zy_opening: zy_opening
        })
    }
}

#[derive(Clone, Debug, Eq)]
pub struct VerifyingKey<E: Engine> {
    pub alpha_x: E::G2Affine,

    pub alpha: E::G2Affine,

    pub neg_h: E::G2Affine,

    pub neg_x_n_minus_d: E::G2Affine,

    pub k_map: Vec<usize>,

    pub n: usize,

    pub q: usize
}

impl<E: Engine> PartialEq for VerifyingKey<E> {
    fn eq(&self, other: &VerifyingKey<E>) -> bool {
        self.alpha_x == other.alpha_x &&
        self.alpha == other.alpha &&
        self.neg_h == other.neg_h &&
        self.neg_x_n_minus_d == other.neg_x_n_minus_d &&
        self.k_map == other.k_map &&
        self.n == other.n &&
        self.q == other.q
    }
}

impl<E: Engine> VerifyingKey<E> {
    pub fn write<W: Write>(
        &self,
        mut writer: W
    ) -> io::Result<()>
    {
        writer.write_all(self.alpha_x.into_uncompressed().as_ref())?;
        writer.write_all(self.alpha.into_uncompressed().as_ref())?;
        writer.write_all(self.neg_h.into_uncompressed().as_ref())?;
        writer.write_all(self.neg_x_n_minus_d.into_uncompressed().as_ref())?;

        writer.write_u32::<BigEndian>(self.k_map.len() as u32)?;
        for k in &self.k_map {
            writer.write_u32::<BigEndian>(*k as u32)?;
        }
        writer.write_u32::<BigEndian>(self.n as u32)?;
        writer.write_u32::<BigEndian>(self.q as u32)?;

        Ok(())
    }

    pub fn read<R: Read>(
        mut reader: R
    ) -> io::Result<Self>
    {
        let mut g2_repr = <E::G2Affine as CurveAffine>::Uncompressed::empty();

        reader.read_exact(g2_repr.as_mut())?;
        let alpha_x = g2_repr.into_affine().map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

        reader.read_exact(g2_repr.as_mut())?;
        let alpha = g2_repr.into_affine().map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

        reader.read_exact(g2_repr.as_mut())?;
        let neg_h = g2_repr.into_affine().map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

        reader.read_exact(g2_repr.as_mut())?;
        let neg_x_n_minus_d = g2_repr.into_affine().map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

        let k_map_len = reader.read_u32::<BigEndian>()? as usize;

        let mut k_map = vec![];

        for _ in 0..k_map_len {
            let k = reader.read_u32::<BigEndian>()? as usize;

            k_map.push(k);
        }

        let n = reader.read_u32::<BigEndian>()? as usize;

        let q = reader.read_u32::<BigEndian>()? as usize;

        Ok(VerifyingKey {
            alpha_x: alpha_x,
            alpha: alpha,
            neg_h: neg_h,
            neg_x_n_minus_d: neg_x_n_minus_d,
            k_map: k_map,
            n: n,
            q: q
        })
    }
}

use crate::sonic::cs::{Backend, Basic, SynthesisDriver};
use crate::sonic::srs::SRS;
use crate::sonic::cs::Circuit as SonicCircuit;
use std::marker::PhantomData;

impl<E: Engine> VerifyingKey<E> {
    pub fn new<C: SonicCircuit<E>, S: SynthesisDriver>(circuit: C, srs: &SRS<E>) -> Result<Self, SynthesisError> {
        struct Preprocess<E: Engine> {
            k_map: Vec<usize>,
            n: usize,
            q: usize,
            _marker: PhantomData<E>
        }

        impl<'a, E: Engine> Backend<E> for &'a mut Preprocess<E> {
            fn new_k_power(&mut self, index: usize) {
                self.k_map.push(index);
            }

            fn new_multiplication_gate(&mut self) {
                self.n += 1;
            }

            fn new_linear_constraint(&mut self) {
                self.q += 1;
            }
        }

        let mut preprocess = Preprocess { k_map: vec![], n: 0, q: 0, _marker: PhantomData };

        S::synthesize(&mut preprocess, &circuit)?;

        Ok(Self {
            alpha_x: srs.h_positive_x_alpha[1],

            alpha: srs.h_positive_x_alpha[0],

            neg_h: {
                let mut tmp = srs.h_negative_x[0];
                tmp.negate();

                tmp
            },

            neg_x_n_minus_d: {
                let mut tmp = srs.h_negative_x[srs.d - preprocess.n];
                tmp.negate();

                tmp
            },

            k_map: preprocess.k_map,
            n: preprocess.n,
            q: preprocess.q
        })
    }
}

pub struct PreparedVerifyingKey<E: Engine> {
    alpha_x: <E::G2Affine as CurveAffine>::Prepared,
    alpha: <E::G2Affine as CurveAffine>::Prepared,
    neg_h: <E::G2Affine as CurveAffine>::Prepared,
    neg_x_n_minus_d: <E::G2Affine as CurveAffine>::Prepared,
    k_map: Vec<usize>,
    n: usize,
    q: usize
}

#[derive(Clone, Eq)]
pub struct Parameters<E: Engine> {
    pub vk: VerifyingKey<E>,

    pub srs: SRS<E>,
    // pub d: usize,

    // // g^{x^0}, g^{x^{-1}}, g^{x^{-2}}, ..., g^{x^{-d}}
    // pub g_negative_x: Arc<Vec<E::G1Affine>>,

    // // g^{x^0}, g^{x^{1}}, g^{x^{2}}, ..., g^{x^{d}}
    // pub g_positive_x: Arc<Vec<E::G1Affine>>,

    // // g^{x^0}, g^{x^{-1}}, g^{x^{-2}}, ..., g^{x^{-d}}
    // pub h_negative_x: Arc<Vec<E::G2Affine>>,

    // // g^{x^0}, g^{x^{1}}, g^{x^{2}}, ..., g^{x^{d}}
    // pub h_positive_x: Arc<Vec<E::G2Affine>>,

    // // alpha*(g^{x^{-1}}, g^{x^{-2}}, ..., g^{x^{-d}})
    // pub g_negative_x_alpha: Arc<Vec<E::G1Affine>>,

    // // alpha*(g^{x^{1}}, g^{x^{2}}, ..., g^{x^{d}})
    // pub g_positive_x_alpha: Arc<Vec<E::G1Affine>>,

    // // alpha*(h^{x^0}, h^{x^{-1}}, g^{x^{-2}}, ..., g^{x^{-d}})
    // pub h_negative_x_alpha: Arc<Vec<E::G2Affine>>,

    // // alpha*(h^{x^0}, g^{x^{1}}, g^{x^{2}}, ..., g^{x^{d}})
    // pub h_positive_x_alpha: Arc<Vec<E::G2Affine>>,
}

impl<E: Engine> PartialEq for Parameters<E> {
    fn eq(&self, other: &Parameters<E>) -> bool {
        self.vk == other.vk &&
        self.srs == other.srs
    }
}

impl<E: Engine> Parameters<E> {
    pub fn write<W: Write>(
        &self,
        mut writer: W
    ) -> io::Result<()>
    {
        self.vk.write(&mut writer)?;
        self.srs.write(&mut writer)?;

        Ok(())
    }

    pub fn read<R: Read>(
        mut reader: R,
        checked: bool
    ) -> io::Result<Self>
    {
        let vk = VerifyingKey::<E>::read(&mut reader)?;
        let srs = SRS::<E>::read(&mut reader, checked)?;

        Ok(Parameters {
            vk: vk,
            srs: srs
        })
    }
}

// pub trait ParameterSource<E: Engine> {
//     type G1Builder: SourceBuilder<E::G1Affine>;
//     type G2Builder: SourceBuilder<E::G2Affine>;

//     fn get_vk(
//         &mut self,
//         num_ic: usize
//     ) -> Result<VerifyingKey<E>, SynthesisError>;
//     fn get_h(
//         &mut self,
//         num_h: usize
//     ) -> Result<Self::G1Builder, SynthesisError>;
//     fn get_l(
//         &mut self,
//         num_l: usize
//     ) -> Result<Self::G1Builder, SynthesisError>;
//     fn get_a(
//         &mut self,
//         num_inputs: usize,
//         num_aux: usize
//     ) -> Result<(Self::G1Builder, Self::G1Builder), SynthesisError>;
//     fn get_b_g1(
//         &mut self,
//         num_inputs: usize,
//         num_aux: usize
//     ) -> Result<(Self::G1Builder, Self::G1Builder), SynthesisError>;
//     fn get_b_g2(
//         &mut self,
//         num_inputs: usize,
//         num_aux: usize
//     ) -> Result<(Self::G2Builder, Self::G2Builder), SynthesisError>;
// }

// impl<'a, E: Engine> ParameterSource<E> for &'a Parameters<E> {
//     type G1Builder = (Arc<Vec<E::G1Affine>>, usize);
//     type G2Builder = (Arc<Vec<E::G2Affine>>, usize);

//     fn get_vk(
//         &mut self,
//         _: usize
//     ) -> Result<VerifyingKey<E>, SynthesisError>
//     {
//         Ok(self.vk.clone())
//     }

//     fn get_h(
//         &mut self,
//         _: usize
//     ) -> Result<Self::G1Builder, SynthesisError>
//     {
//         Ok((self.h.clone(), 0))
//     }

//     fn get_l(
//         &mut self,
//         _: usize
//     ) -> Result<Self::G1Builder, SynthesisError>
//     {
//         Ok((self.l.clone(), 0))
//     }

//     fn get_a(
//         &mut self,
//         num_inputs: usize,
//         _: usize
//     ) -> Result<(Self::G1Builder, Self::G1Builder), SynthesisError>
//     {
//         Ok(((self.a.clone(), 0), (self.a.clone(), num_inputs)))
//     }

//     fn get_b_g1(
//         &mut self,
//         num_inputs: usize,
//         _: usize
//     ) -> Result<(Self::G1Builder, Self::G1Builder), SynthesisError>
//     {
//         Ok(((self.b_g1.clone(), 0), (self.b_g1.clone(), num_inputs)))
//     }

//     fn get_b_g2(
//         &mut self,
//         num_inputs: usize,
//         _: usize
//     ) -> Result<(Self::G2Builder, Self::G2Builder), SynthesisError>
//     {
//         Ok(((self.b_g2.clone(), 0), (self.b_g2.clone(), num_inputs)))
//     }
// }

// #[cfg(test)]
// mod test_with_bls12_381 {
//     use super::*;
//     use {Circuit, SynthesisError, ConstraintSystem};

//     use rand::{Rand, thread_rng};
//     use ff::{Field};
//     use pairing::bls12_381::{Bls12, Fr};

//     #[test]
//     fn serialization() {
//         struct MySillyCircuit<E: Engine> {
//             a: Option<E::Fr>,
//             b: Option<E::Fr>
//         }

//         impl<E: Engine> Circuit<E> for MySillyCircuit<E> {
//             fn synthesize<CS: ConstraintSystem<E>>(
//                 self,
//                 cs: &mut CS
//             ) -> Result<(), SynthesisError>
//             {
//                 let a = cs.alloc(|| "a", || self.a.ok_or(SynthesisError::AssignmentMissing))?;
//                 let b = cs.alloc(|| "b", || self.b.ok_or(SynthesisError::AssignmentMissing))?;
//                 let c = cs.alloc_input(|| "c", || {
//                     let mut a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
//                     let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;

//                     a.mul_assign(&b);
//                     Ok(a)
//                 })?;

//                 cs.enforce(
//                     || "a*b=c",
//                     |lc| lc + a,
//                     |lc| lc + b,
//                     |lc| lc + c
//                 );

//                 Ok(())
//             }
//         }

//         let rng = &mut thread_rng();

//         let params = generate_random_parameters::<Bls12, _, _>(
//             MySillyCircuit { a: None, b: None },
//             rng
//         ).unwrap();

//         {
//             let mut v = vec![];

//             params.write(&mut v).unwrap();
//             assert_eq!(v.len(), 2136);

//             let de_params = Parameters::read(&v[..], true).unwrap();
//             assert!(params == de_params);

//             let de_params = Parameters::read(&v[..], false).unwrap();
//             assert!(params == de_params);
//         }

//         let pvk = prepare_verifying_key::<Bls12>(&params.vk);

//         for _ in 0..100 {
//             let a = Fr::rand(rng);
//             let b = Fr::rand(rng);
//             let mut c = a;
//             c.mul_assign(&b);

//             let proof = create_random_proof(
//                 MySillyCircuit {
//                     a: Some(a),
//                     b: Some(b)
//                 },
//                 &params,
//                 rng
//             ).unwrap();

//             let mut v = vec![];
//             proof.write(&mut v).unwrap();

//             assert_eq!(v.len(), 192);

//             let de_proof = Proof::read(&v[..]).unwrap();
//             assert!(proof == de_proof);

//             assert!(verify_proof(&pvk, &proof, &[c]).unwrap());
//             assert!(!verify_proof(&pvk, &proof, &[a]).unwrap());
//         }
//     }
// }