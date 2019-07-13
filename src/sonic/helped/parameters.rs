use crate::pairing::ff::{
    Field,
    PrimeField, 
    PrimeFieldRepr
};

use crate::pairing::{
    Engine,
    CurveAffine,
    EncodedPoint
};

use crate::{
    SynthesisError
};

use crate::source::SourceBuilder;
use std::io::{self, Read, Write};
use std::sync::Arc;
use byteorder::{BigEndian, WriteBytesExt, ReadBytesExt};

pub const NUM_BLINDINGS: usize = 6;
// pub const NUM_BLINDINGS: usize = 0;

#[derive(Clone, Debug, Eq)]
pub struct SxyAdvice<E: Engine> {
    pub s: E::G1Affine,
    pub opening: E::G1Affine,
    pub szy: E::Fr,
}

impl<E: Engine> PartialEq for SxyAdvice<E> {
    fn eq(&self, other: &SxyAdvice<E>) -> bool {
        self.s == other.s &&
        self.opening == other.opening &&
        self.szy == other.szy
    }
}

#[derive(Clone, Debug, Eq)]
pub struct Proof<E: Engine> {
    pub r: E::G1Affine,
    pub t: E::G1Affine,
    pub rz: E::Fr,
    pub rzy: E::Fr,
    pub z_opening: E::G1Affine,
    pub zy_opening: E::G1Affine
}

impl<E: Engine> PartialEq for Proof<E> {
    fn eq(&self, other: &Proof<E>) -> bool {
        self.r == other.r &&
        self.t == other.t &&
        self.rz == other.rz &&
        self.rzy == other.rzy &&
        self.z_opening == other.z_opening &&
        self.zy_opening == other.zy_opening
    }
}

impl<E: Engine> Proof<E> {
    pub fn write<W: Write>(
        &self,
        mut writer: W
    ) -> io::Result<()>
    {
        use crate::pairing::ff::{PrimeField, PrimeFieldRepr};
        writer.write_all(self.r.into_compressed().as_ref())?;
        writer.write_all(self.t.into_compressed().as_ref())?;
        let mut buffer = vec![];
        self.rz.into_repr().write_be(&mut buffer)?;
        writer.write_all(&buffer[..])?;
        let mut buffer = vec![];
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

use crate::sonic::cs::{Backend, SynthesisDriver};
use crate::sonic::srs::SRS;
use crate::sonic::cs::Circuit as SonicCircuit;
use crate::sonic::sonic::{Basic, Preprocess};
use std::marker::PhantomData;


impl<E: Engine> VerifyingKey<E> {
    pub fn new<C: SonicCircuit<E>, S: SynthesisDriver>(circuit: C, srs: &SRS<E>) -> Result<Self, SynthesisError> {
        let mut preprocess = Preprocess::new();

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

#[test]
fn parameters_generation() {
    use crate::{ConstraintSystem, Circuit};

    use crate::pairing::bls12_381::{Bls12, Fr};

    #[derive(Clone)]
    struct MySillyCircuit<E: Engine> {
        a: Option<E::Fr>,
        b: Option<E::Fr>
    }

    impl<E: Engine> Circuit<E> for MySillyCircuit<E> {
        fn synthesize<CS: ConstraintSystem<E>>(
            self,
            cs: &mut CS
        ) -> Result<(), SynthesisError>
        {
            let a = cs.alloc(|| "a", || self.a.ok_or(SynthesisError::AssignmentMissing))?;
            let b = cs.alloc(|| "b", || self.b.ok_or(SynthesisError::AssignmentMissing))?;
            let c = cs.alloc_input(|| "c", || {
                let mut a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
                let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;

                a.mul_assign(&b);
                Ok(a)
            })?;

            cs.enforce(
                || "a*b=c",
                |lc| lc + a,
                |lc| lc + b,
                |lc| lc + c
            );

            Ok(())
        }
    }

    use rand::{Rng, Rand, thread_rng};
    use super::{generate_parameters, get_circuit_parameters, generate_srs, generate_parameters_on_srs_and_information};
    use super::adapted_prover::create_proof;

    let info = get_circuit_parameters::<Bls12, _>(MySillyCircuit { a: None, b: None }).expect("Must get circuit info");
    println!("{:?}", info);
    let rng = &mut thread_rng();

    let x: Fr = rng.gen();
    let alpha: Fr = rng.gen();

    let params = generate_parameters::<Bls12, _>(MySillyCircuit { a: None, b: None }, alpha, x).unwrap();
    let srs = generate_srs::<Bls12>(alpha, x, info.n * 100).unwrap();
    let naive_srs = SRS::<Bls12>::new(
        info.n * 100,
        x,
        alpha,
    );

    assert!(srs == naive_srs);

    let params_on_srs = generate_parameters_on_srs_and_information::<Bls12>(&srs, info.clone()).unwrap();

    assert!(params == params_on_srs);

    {
        let mut v = vec![];

        params.write(&mut v).unwrap();

        let de_params = Parameters::read(&v[..], true).unwrap();
        assert!(params == de_params);

        let de_params = Parameters::read(&v[..], false).unwrap();
        assert!(params == de_params);
    }

    for _ in 0..100 {
        let a = Fr::rand(rng);
        let b = Fr::rand(rng);
        let mut c = a;
        c.mul_assign(&b);

        let proof = create_proof (
            MySillyCircuit {
                a: Some(a),
                b: Some(b)
            },
            &params,
        ).unwrap();

        let mut v = vec![];
        proof.write(&mut v).unwrap();

        assert_eq!(v.len(), 256);

        let de_proof = Proof::read(&v[..]).unwrap();
        assert!(proof == de_proof);

        // assert!(verify_proof(&pvk, &proof, &[c]).unwrap());
        // assert!(!verify_proof(&pvk, &proof, &[a]).unwrap());
    }
}