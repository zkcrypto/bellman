//! The [Groth16] proving system.
//!
//! [Groth16]: https://eprint.iacr.org/2016/260

use group::{prime::PrimeCurveAffine, GroupEncoding, UncompressedEncoding};
use pairing::{Engine, MultiMillerLoop};

use crate::SynthesisError;

use crate::multiexp::SourceBuilder;
use byteorder::{BigEndian, ReadBytesExt, WriteBytesExt};
use std::io::{self, Read, Write};
use std::sync::Arc;

#[cfg(test)]
mod tests;

mod generator;
mod prover;
mod verifier;

pub use self::generator::*;
pub use self::prover::*;
pub use self::verifier::*;

#[derive(Clone)]
pub struct Proof<E: Engine> {
    pub a: E::G1Affine,
    pub b: E::G2Affine,
    pub c: E::G1Affine,
}

impl<E: Engine> PartialEq for Proof<E> {
    fn eq(&self, other: &Self) -> bool {
        self.a == other.a && self.b == other.b && self.c == other.c
    }
}

impl<E: Engine> Proof<E> {
    pub fn write<W: Write>(&self, mut writer: W) -> io::Result<()> {
        writer.write_all(self.a.to_bytes().as_ref())?;
        writer.write_all(self.b.to_bytes().as_ref())?;
        writer.write_all(self.c.to_bytes().as_ref())?;

        Ok(())
    }

    pub fn read<R: Read>(mut reader: R) -> io::Result<Self> {
        let read_g1 = |reader: &mut R| -> io::Result<E::G1Affine> {
            let mut g1_repr = <E::G1Affine as GroupEncoding>::Repr::default();
            reader.read_exact(g1_repr.as_mut())?;

            let affine = E::G1Affine::from_bytes(&g1_repr);
            let affine = if affine.is_some().into() {
                Ok(affine.unwrap())
            } else {
                Err(io::Error::new(io::ErrorKind::InvalidData, "invalid G1"))
            };

            affine.and_then(|e| {
                if e.is_identity().into() {
                    Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "point at infinity",
                    ))
                } else {
                    Ok(e)
                }
            })
        };

        let read_g2 = |reader: &mut R| -> io::Result<E::G2Affine> {
            let mut g2_repr = <E::G2Affine as GroupEncoding>::Repr::default();
            reader.read_exact(g2_repr.as_mut())?;

            let affine = E::G2Affine::from_bytes(&g2_repr);
            let affine = if affine.is_some().into() {
                Ok(affine.unwrap())
            } else {
                Err(io::Error::new(io::ErrorKind::InvalidData, "invalid G2"))
            };

            affine.and_then(|e| {
                if e.is_identity().into() {
                    Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "point at infinity",
                    ))
                } else {
                    Ok(e)
                }
            })
        };

        let a = read_g1(&mut reader)?;
        let b = read_g2(&mut reader)?;
        let c = read_g1(&mut reader)?;

        Ok(Proof { a, b, c })
    }
}

#[derive(Clone)]
pub struct VerifyingKey<E: Engine> {
    // alpha in g1 for verifying and for creating A/C elements of
    // proof. Never the point at infinity.
    pub alpha_g1: E::G1Affine,

    // beta in g1 and g2 for verifying and for creating B/C elements
    // of proof. Never the point at infinity.
    pub beta_g1: E::G1Affine,
    pub beta_g2: E::G2Affine,

    // gamma in g2 for verifying. Never the point at infinity.
    pub gamma_g2: E::G2Affine,

    // delta in g1/g2 for verifying and proving, essentially the magic
    // trapdoor that forces the prover to evaluate the C element of the
    // proof with only components from the CRS. Never the point at
    // infinity.
    pub delta_g1: E::G1Affine,
    pub delta_g2: E::G2Affine,

    // Elements of the form (beta * u_i(tau) + alpha v_i(tau) + w_i(tau)) / gamma
    // for all public inputs. Because all public inputs have a dummy constraint,
    // this is the same size as the number of inputs, and never contains points
    // at infinity.
    pub ic: Vec<E::G1Affine>,
}

impl<E: Engine> PartialEq for VerifyingKey<E> {
    fn eq(&self, other: &Self) -> bool {
        self.alpha_g1 == other.alpha_g1
            && self.beta_g1 == other.beta_g1
            && self.beta_g2 == other.beta_g2
            && self.gamma_g2 == other.gamma_g2
            && self.delta_g1 == other.delta_g1
            && self.delta_g2 == other.delta_g2
            && self.ic == other.ic
    }
}

impl<E: Engine> VerifyingKey<E> {
    pub fn write<W: Write>(&self, mut writer: W) -> io::Result<()> {
        writer.write_all(self.alpha_g1.to_uncompressed().as_ref())?;
        writer.write_all(self.beta_g1.to_uncompressed().as_ref())?;
        writer.write_all(self.beta_g2.to_uncompressed().as_ref())?;
        writer.write_all(self.gamma_g2.to_uncompressed().as_ref())?;
        writer.write_all(self.delta_g1.to_uncompressed().as_ref())?;
        writer.write_all(self.delta_g2.to_uncompressed().as_ref())?;
        writer.write_u32::<BigEndian>(self.ic.len() as u32)?;
        for ic in &self.ic {
            writer.write_all(ic.to_uncompressed().as_ref())?;
        }

        Ok(())
    }

    pub fn read<R: Read>(mut reader: R) -> io::Result<Self> {
        let read_g1 = |reader: &mut R| -> io::Result<E::G1Affine> {
            let mut g1_repr = <E::G1Affine as UncompressedEncoding>::Uncompressed::default();
            reader.read_exact(g1_repr.as_mut())?;

            let affine = E::G1Affine::from_uncompressed(&g1_repr);
            if affine.is_some().into() {
                Ok(affine.unwrap())
            } else {
                Err(io::Error::new(io::ErrorKind::InvalidData, "invalid G1"))
            }
        };

        let read_g2 = |reader: &mut R| -> io::Result<E::G2Affine> {
            let mut g2_repr = <E::G2Affine as UncompressedEncoding>::Uncompressed::default();
            reader.read_exact(g2_repr.as_mut())?;

            let affine = E::G2Affine::from_uncompressed(&g2_repr);
            if affine.is_some().into() {
                Ok(affine.unwrap())
            } else {
                Err(io::Error::new(io::ErrorKind::InvalidData, "invalid G2"))
            }
        };

        let alpha_g1 = read_g1(&mut reader)?;
        let beta_g1 = read_g1(&mut reader)?;
        let beta_g2 = read_g2(&mut reader)?;
        let gamma_g2 = read_g2(&mut reader)?;
        let delta_g1 = read_g1(&mut reader)?;
        let delta_g2 = read_g2(&mut reader)?;

        let ic_len = reader.read_u32::<BigEndian>()? as usize;

        let mut ic = vec![];

        for _ in 0..ic_len {
            let g1 = read_g1(&mut reader).and_then(|e| {
                if e.is_identity().into() {
                    Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "point at infinity",
                    ))
                } else {
                    Ok(e)
                }
            })?;

            ic.push(g1);
        }

        Ok(VerifyingKey {
            alpha_g1,
            beta_g1,
            beta_g2,
            gamma_g2,
            delta_g1,
            delta_g2,
            ic,
        })
    }
}

#[derive(Clone)]
pub struct Parameters<E: Engine> {
    pub vk: VerifyingKey<E>,

    // Elements of the form ((tau^i * t(tau)) / delta) for i between 0 and
    // m-2 inclusive. Never contains points at infinity.
    pub h: Arc<Vec<E::G1Affine>>,

    // Elements of the form (beta * u_i(tau) + alpha v_i(tau) + w_i(tau)) / delta
    // for all auxiliary inputs. Variables can never be unconstrained, so this
    // never contains points at infinity.
    pub l: Arc<Vec<E::G1Affine>>,

    // QAP "A" polynomials evaluated at tau in the Lagrange basis. Never contains
    // points at infinity: polynomials that evaluate to zero are omitted from
    // the CRS and the prover can deterministically skip their evaluation.
    pub a: Arc<Vec<E::G1Affine>>,

    // QAP "B" polynomials evaluated at tau in the Lagrange basis. Needed in
    // G1 and G2 for C/B queries, respectively. Never contains points at
    // infinity for the same reason as the "A" polynomials.
    pub b_g1: Arc<Vec<E::G1Affine>>,
    pub b_g2: Arc<Vec<E::G2Affine>>,
}

impl<E: Engine> PartialEq for Parameters<E> {
    fn eq(&self, other: &Self) -> bool {
        self.vk == other.vk
            && self.h == other.h
            && self.l == other.l
            && self.a == other.a
            && self.b_g1 == other.b_g1
            && self.b_g2 == other.b_g2
    }
}

impl<E: Engine> Parameters<E> {
    pub fn write<W: Write>(&self, mut writer: W) -> io::Result<()> {
        self.vk.write(&mut writer)?;

        writer.write_u32::<BigEndian>(self.h.len() as u32)?;
        for g in &self.h[..] {
            writer.write_all(g.to_uncompressed().as_ref())?;
        }

        writer.write_u32::<BigEndian>(self.l.len() as u32)?;
        for g in &self.l[..] {
            writer.write_all(g.to_uncompressed().as_ref())?;
        }

        writer.write_u32::<BigEndian>(self.a.len() as u32)?;
        for g in &self.a[..] {
            writer.write_all(g.to_uncompressed().as_ref())?;
        }

        writer.write_u32::<BigEndian>(self.b_g1.len() as u32)?;
        for g in &self.b_g1[..] {
            writer.write_all(g.to_uncompressed().as_ref())?;
        }

        writer.write_u32::<BigEndian>(self.b_g2.len() as u32)?;
        for g in &self.b_g2[..] {
            writer.write_all(g.to_uncompressed().as_ref())?;
        }

        Ok(())
    }

    pub fn read<R: Read>(mut reader: R, checked: bool) -> io::Result<Self> {
        let read_g1 = |reader: &mut R| -> io::Result<E::G1Affine> {
            let mut repr = <E::G1Affine as UncompressedEncoding>::Uncompressed::default();
            reader.read_exact(repr.as_mut())?;

            let affine = if checked {
                E::G1Affine::from_uncompressed(&repr)
            } else {
                E::G1Affine::from_uncompressed_unchecked(&repr)
            };

            let affine = if affine.is_some().into() {
                Ok(affine.unwrap())
            } else {
                Err(io::Error::new(io::ErrorKind::InvalidData, "invalid G1"))
            };

            affine.and_then(|e| {
                if e.is_identity().into() {
                    Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "point at infinity",
                    ))
                } else {
                    Ok(e)
                }
            })
        };

        let read_g2 = |reader: &mut R| -> io::Result<E::G2Affine> {
            let mut repr = <E::G2Affine as UncompressedEncoding>::Uncompressed::default();
            reader.read_exact(repr.as_mut())?;

            let affine = if checked {
                E::G2Affine::from_uncompressed(&repr)
            } else {
                E::G2Affine::from_uncompressed_unchecked(&repr)
            };

            let affine = if affine.is_some().into() {
                Ok(affine.unwrap())
            } else {
                Err(io::Error::new(io::ErrorKind::InvalidData, "invalid G2"))
            };

            affine.and_then(|e| {
                if e.is_identity().into() {
                    Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "point at infinity",
                    ))
                } else {
                    Ok(e)
                }
            })
        };

        let vk = VerifyingKey::<E>::read(&mut reader)?;

        let mut h = vec![];
        let mut l = vec![];
        let mut a = vec![];
        let mut b_g1 = vec![];
        let mut b_g2 = vec![];

        {
            let len = reader.read_u32::<BigEndian>()? as usize;
            for _ in 0..len {
                h.push(read_g1(&mut reader)?);
            }
        }

        {
            let len = reader.read_u32::<BigEndian>()? as usize;
            for _ in 0..len {
                l.push(read_g1(&mut reader)?);
            }
        }

        {
            let len = reader.read_u32::<BigEndian>()? as usize;
            for _ in 0..len {
                a.push(read_g1(&mut reader)?);
            }
        }

        {
            let len = reader.read_u32::<BigEndian>()? as usize;
            for _ in 0..len {
                b_g1.push(read_g1(&mut reader)?);
            }
        }

        {
            let len = reader.read_u32::<BigEndian>()? as usize;
            for _ in 0..len {
                b_g2.push(read_g2(&mut reader)?);
            }
        }

        Ok(Parameters {
            vk,
            h: Arc::new(h),
            l: Arc::new(l),
            a: Arc::new(a),
            b_g1: Arc::new(b_g1),
            b_g2: Arc::new(b_g2),
        })
    }
}

pub struct PreparedVerifyingKey<E: MultiMillerLoop> {
    /// Pairing result of alpha*beta
    alpha_g1_beta_g2: E::Gt,
    /// -gamma in G2
    neg_gamma_g2: E::G2Prepared,
    /// -delta in G2
    neg_delta_g2: E::G2Prepared,
    /// Copy of IC from `VerifiyingKey`.
    ic: Vec<E::G1Affine>,
}

pub trait ParameterSource<E: Engine> {
    type G1Builder: SourceBuilder<E::G1Affine>;
    type G2Builder: SourceBuilder<E::G2Affine>;

    fn get_vk(&mut self, num_ic: usize) -> Result<VerifyingKey<E>, SynthesisError>;
    fn get_h(&mut self, num_h: usize) -> Result<Self::G1Builder, SynthesisError>;
    fn get_l(&mut self, num_l: usize) -> Result<Self::G1Builder, SynthesisError>;
    fn get_a(
        &mut self,
        num_inputs: usize,
        num_aux: usize,
    ) -> Result<(Self::G1Builder, Self::G1Builder), SynthesisError>;
    fn get_b_g1(
        &mut self,
        num_inputs: usize,
        num_aux: usize,
    ) -> Result<(Self::G1Builder, Self::G1Builder), SynthesisError>;
    fn get_b_g2(
        &mut self,
        num_inputs: usize,
        num_aux: usize,
    ) -> Result<(Self::G2Builder, Self::G2Builder), SynthesisError>;
}

impl<'a, E: Engine> ParameterSource<E> for &'a Parameters<E> {
    type G1Builder = (Arc<Vec<E::G1Affine>>, usize);
    type G2Builder = (Arc<Vec<E::G2Affine>>, usize);

    fn get_vk(&mut self, _: usize) -> Result<VerifyingKey<E>, SynthesisError> {
        Ok(self.vk.clone())
    }

    fn get_h(&mut self, _: usize) -> Result<Self::G1Builder, SynthesisError> {
        Ok((self.h.clone(), 0))
    }

    fn get_l(&mut self, _: usize) -> Result<Self::G1Builder, SynthesisError> {
        Ok((self.l.clone(), 0))
    }

    fn get_a(
        &mut self,
        num_inputs: usize,
        _: usize,
    ) -> Result<(Self::G1Builder, Self::G1Builder), SynthesisError> {
        Ok(((self.a.clone(), 0), (self.a.clone(), num_inputs)))
    }

    fn get_b_g1(
        &mut self,
        num_inputs: usize,
        _: usize,
    ) -> Result<(Self::G1Builder, Self::G1Builder), SynthesisError> {
        Ok(((self.b_g1.clone(), 0), (self.b_g1.clone(), num_inputs)))
    }

    fn get_b_g2(
        &mut self,
        num_inputs: usize,
        _: usize,
    ) -> Result<(Self::G2Builder, Self::G2Builder), SynthesisError> {
        Ok(((self.b_g2.clone(), 0), (self.b_g2.clone(), num_inputs)))
    }
}

#[cfg(test)]
mod test_with_bls12_381 {
    use super::*;
    use crate::{Circuit, ConstraintSystem, SynthesisError};

    use bls12_381::{Bls12, Scalar};
    use ff::{Field, PrimeField};
    use rand::thread_rng;
    use std::ops::MulAssign;

    #[test]
    fn serialization() {
        struct MySillyCircuit<Scalar: PrimeField> {
            a: Option<Scalar>,
            b: Option<Scalar>,
        }

        impl<Scalar: PrimeField> Circuit<Scalar> for MySillyCircuit<Scalar> {
            fn synthesize<CS: ConstraintSystem<Scalar>>(
                self,
                cs: &mut CS,
            ) -> Result<(), SynthesisError> {
                let a = cs.alloc(|| "a", || self.a.ok_or(SynthesisError::AssignmentMissing))?;
                let b = cs.alloc(|| "b", || self.b.ok_or(SynthesisError::AssignmentMissing))?;
                let c = cs.alloc_input(
                    || "c",
                    || {
                        let mut a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
                        let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;

                        a.mul_assign(&b);
                        Ok(a)
                    },
                )?;

                cs.enforce(|| "a*b=c", |lc| lc + a, |lc| lc + b, |lc| lc + c);

                Ok(())
            }
        }

        let mut rng = thread_rng();

        let params = generate_random_parameters::<Bls12, _, _>(
            MySillyCircuit { a: None, b: None },
            &mut rng,
        )
        .unwrap();

        {
            let mut v = vec![];

            params.write(&mut v).unwrap();
            assert_eq!(v.len(), 2136);

            let de_params = Parameters::read(&v[..], true).unwrap();
            assert!(params == de_params);

            let de_params = Parameters::read(&v[..], false).unwrap();
            assert!(params == de_params);
        }

        let pvk = prepare_verifying_key::<Bls12>(&params.vk);

        for _ in 0..100 {
            let a = Scalar::random(&mut rng);
            let b = Scalar::random(&mut rng);
            let mut c = a;
            c.mul_assign(&b);

            let proof = create_random_proof(
                MySillyCircuit {
                    a: Some(a),
                    b: Some(b),
                },
                &params,
                &mut rng,
            )
            .unwrap();

            let mut v = vec![];
            proof.write(&mut v).unwrap();

            assert_eq!(v.len(), 192);

            let de_proof = Proof::read(&v[..]).unwrap();
            assert!(proof == de_proof);

            assert!(verify_proof(&pvk, &proof, &[c]).is_ok());
            assert!(verify_proof(&pvk, &proof, &[a]).is_err());
        }
    }
}
