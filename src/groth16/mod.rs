//! The [Groth16] proving system.
//!
//! [Groth16]: https://eprint.iacr.org/2016/260

use groupy::{CurveAffine, EncodedPoint};
use paired::{Engine, PairingCurveAffine};

use crate::multiexp::SourceBuilder;
use crate::SynthesisError;

use byteorder::{BigEndian, ReadBytesExt, WriteBytesExt};
use memmap::{Mmap, MmapOptions};
use std::fs::File;
use std::io::{self, Read, Write};
use std::mem;
use std::ops::Range;
use std::path::PathBuf;
use std::sync::Arc;

#[cfg(test)]
mod tests;

mod ext;
mod generator;
mod mapped_params;
mod prover;
mod verifier;

pub use self::ext::*;
pub use self::generator::*;
pub use self::mapped_params::*;
pub use self::prover::*;
pub use self::verifier::*;

#[derive(Clone, Debug)]
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
        writer.write_all(self.a.into_compressed().as_ref())?;
        writer.write_all(self.b.into_compressed().as_ref())?;
        writer.write_all(self.c.into_compressed().as_ref())?;

        Ok(())
    }

    pub fn read<R: Read>(mut reader: R) -> io::Result<Self> {
        let mut g1_repr = <E::G1Affine as CurveAffine>::Compressed::empty();
        let mut g2_repr = <E::G2Affine as CurveAffine>::Compressed::empty();

        reader.read_exact(g1_repr.as_mut())?;
        let a = g1_repr
            .into_affine()
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
            .and_then(|e| {
                if e.is_zero() {
                    Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "point at infinity",
                    ))
                } else {
                    Ok(e)
                }
            })?;

        reader.read_exact(g2_repr.as_mut())?;
        let b = g2_repr
            .into_affine()
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
            .and_then(|e| {
                if e.is_zero() {
                    Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "point at infinity",
                    ))
                } else {
                    Ok(e)
                }
            })?;

        reader.read_exact(g1_repr.as_mut())?;
        let c = g1_repr
            .into_affine()
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
            .and_then(|e| {
                if e.is_zero() {
                    Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "point at infinity",
                    ))
                } else {
                    Ok(e)
                }
            })?;

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
        writer.write_all(self.alpha_g1.into_uncompressed().as_ref())?;
        writer.write_all(self.beta_g1.into_uncompressed().as_ref())?;
        writer.write_all(self.beta_g2.into_uncompressed().as_ref())?;
        writer.write_all(self.gamma_g2.into_uncompressed().as_ref())?;
        writer.write_all(self.delta_g1.into_uncompressed().as_ref())?;
        writer.write_all(self.delta_g2.into_uncompressed().as_ref())?;
        writer.write_u32::<BigEndian>(self.ic.len() as u32)?;
        for ic in &self.ic {
            writer.write_all(ic.into_uncompressed().as_ref())?;
        }

        Ok(())
    }

    pub fn read<R: Read>(mut reader: R) -> io::Result<Self> {
        let mut g1_repr = <E::G1Affine as CurveAffine>::Uncompressed::empty();
        let mut g2_repr = <E::G2Affine as CurveAffine>::Uncompressed::empty();

        reader.read_exact(g1_repr.as_mut())?;
        let alpha_g1 = g1_repr
            .into_affine()
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

        reader.read_exact(g1_repr.as_mut())?;
        let beta_g1 = g1_repr
            .into_affine()
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

        reader.read_exact(g2_repr.as_mut())?;
        let beta_g2 = g2_repr
            .into_affine()
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

        reader.read_exact(g2_repr.as_mut())?;
        let gamma_g2 = g2_repr
            .into_affine()
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

        reader.read_exact(g1_repr.as_mut())?;
        let delta_g1 = g1_repr
            .into_affine()
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

        reader.read_exact(g2_repr.as_mut())?;
        let delta_g2 = g2_repr
            .into_affine()
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

        let ic_len = reader.read_u32::<BigEndian>()? as usize;

        let mut ic = vec![];

        for _ in 0..ic_len {
            reader.read_exact(g1_repr.as_mut())?;
            let g1 = g1_repr
                .into_affine()
                .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
                .and_then(|e| {
                    if e.is_zero() {
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

    pub fn read_mmap(mmap: &Mmap, offset: &mut usize) -> io::Result<Self> {
        let u32_len = mem::size_of::<u32>();
        let g1_len = mem::size_of::<<E::G1Affine as CurveAffine>::Uncompressed>();
        let g2_len = mem::size_of::<<E::G2Affine as CurveAffine>::Uncompressed>();

        let read_g1 = |mmap: &Mmap,
                       offset: &mut usize|
         -> Result<<E as paired::Engine>::G1Affine, std::io::Error> {
            let ptr = &mmap[*offset..*offset + g1_len];
            // Safety: this operation is safe, because it's simply
            // casting to a known struct at the correct offset, given
            // the structure of the on-disk data.
            let g1_repr: <E::G1Affine as CurveAffine>::Uncompressed = unsafe {
                *(ptr as *const [u8] as *const <E::G1Affine as CurveAffine>::Uncompressed)
            };

            *offset += g1_len;
            g1_repr
                .into_affine()
                .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
        };

        let read_g2 = |mmap: &Mmap,
                       offset: &mut usize|
         -> Result<<E as paired::Engine>::G2Affine, std::io::Error> {
            let ptr = &mmap[*offset..*offset + g2_len];
            // Safety: this operation is safe, because it's simply
            // casting to a known struct at the correct offset, given
            // the structure of the on-disk data.
            let g2_repr: <E::G2Affine as CurveAffine>::Uncompressed = unsafe {
                *(ptr as *const [u8] as *const <E::G2Affine as CurveAffine>::Uncompressed)
            };

            *offset += g2_len;
            g2_repr
                .into_affine()
                .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
        };

        let alpha_g1 = read_g1(&mmap, &mut *offset)?;
        let beta_g1 = read_g1(&mmap, &mut *offset)?;
        let beta_g2 = read_g2(&mmap, &mut *offset)?;
        let gamma_g2 = read_g2(&mmap, &mut *offset)?;
        let delta_g1 = read_g1(&mmap, &mut *offset)?;
        let delta_g2 = read_g2(&mmap, &mut *offset)?;

        let mut raw_ic_len = &mmap[*offset..*offset + u32_len];
        let ic_len = raw_ic_len.read_u32::<BigEndian>()? as usize;
        *offset += u32_len;

        let mut ic = vec![];

        for _ in 0..ic_len {
            let g1_repr = read_g1(&mmap, &mut *offset);
            let g1 = g1_repr.and_then(|e| {
                if e.is_zero() {
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
            writer.write_all(g.into_uncompressed().as_ref())?;
        }

        writer.write_u32::<BigEndian>(self.l.len() as u32)?;
        for g in &self.l[..] {
            writer.write_all(g.into_uncompressed().as_ref())?;
        }

        writer.write_u32::<BigEndian>(self.a.len() as u32)?;
        for g in &self.a[..] {
            writer.write_all(g.into_uncompressed().as_ref())?;
        }

        writer.write_u32::<BigEndian>(self.b_g1.len() as u32)?;
        for g in &self.b_g1[..] {
            writer.write_all(g.into_uncompressed().as_ref())?;
        }

        writer.write_u32::<BigEndian>(self.b_g2.len() as u32)?;
        for g in &self.b_g2[..] {
            writer.write_all(g.into_uncompressed().as_ref())?;
        }

        Ok(())
    }

    // Quickly iterates through the parameter file, recording all
    // parameter offsets and caches the verifying key (vk) for quick
    // access via reference.
    pub fn build_mapped_parameters(
        param_file: PathBuf,
        checked: bool,
    ) -> io::Result<MappedParameters<E>> {
        let mut offset: usize = 0;
        let params = File::open(&param_file)?;
        let mmap = unsafe { MmapOptions::new().map(&params)? };

        let u32_len = mem::size_of::<u32>();
        let g1_len = mem::size_of::<<E::G1Affine as CurveAffine>::Uncompressed>();
        let g2_len = mem::size_of::<<E::G2Affine as CurveAffine>::Uncompressed>();

        let read_length = |mmap: &Mmap, offset: &mut usize| -> Result<usize, std::io::Error> {
            let mut raw_len = &mmap[*offset..*offset + u32_len];
            *offset += u32_len;

            match raw_len.read_u32::<BigEndian>() {
                Ok(len) => Ok(len as usize),
                Err(err) => Err(err),
            }
        };

        let get_offsets = |mmap: &Mmap,
                           offset: &mut usize,
                           param: &mut Vec<Range<usize>>,
                           range_len: usize|
         -> Result<(), std::io::Error> {
            let len = read_length(&mmap, &mut *offset)?;
            for _ in 0..len {
                (*param).push(Range {
                    start: *offset,
                    end: *offset + range_len,
                });
                *offset += range_len;
            }

            Ok(())
        };

        let vk = VerifyingKey::<E>::read_mmap(&mmap, &mut offset)?;

        let mut h = vec![];
        let mut l = vec![];
        let mut a = vec![];
        let mut b_g1 = vec![];
        let mut b_g2 = vec![];

        get_offsets(&mmap, &mut offset, &mut h, g1_len)?;
        get_offsets(&mmap, &mut offset, &mut l, g1_len)?;
        get_offsets(&mmap, &mut offset, &mut a, g1_len)?;
        get_offsets(&mmap, &mut offset, &mut b_g1, g1_len)?;
        get_offsets(&mmap, &mut offset, &mut b_g2, g2_len)?;

        Ok(MappedParameters {
            param_file,
            vk,
            h,
            l,
            a,
            b_g1,
            b_g2,
            checked,
            _e: Default::default(),
        })
    }

    // This method is provided as a proof of concept, but isn't
    // advantageous to use (can be called by read_cached_params in
    // rust-fil-proofs repo).  It's equivalent to the existing read
    // method, in that it loads all parameters to RAM.
    pub fn read_mmap(mmap: &Mmap, checked: bool) -> io::Result<Self> {
        let u32_len = mem::size_of::<u32>();
        let g1_len = mem::size_of::<<E::G1Affine as CurveAffine>::Uncompressed>();
        let g2_len = mem::size_of::<<E::G2Affine as CurveAffine>::Uncompressed>();

        let read_g1 = |mmap: &Mmap, offset: &mut usize| -> io::Result<E::G1Affine> {
            let ptr = &mmap[*offset..*offset + g1_len];
            *offset += g1_len;
            // Safety: this operation is safe, because it's simply
            // casting to a known struct at the correct offset, given
            // the structure of the on-disk data.
            let repr: <E::G1Affine as CurveAffine>::Uncompressed = unsafe {
                *(ptr as *const [u8] as *const <E::G1Affine as CurveAffine>::Uncompressed)
            };

            if checked {
                repr.into_affine()
            } else {
                repr.into_affine_unchecked()
            }
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
            .and_then(|e| {
                if e.is_zero() {
                    Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "point at infinity",
                    ))
                } else {
                    Ok(e)
                }
            })
        };

        let read_g2 = |mmap: &Mmap, offset: &mut usize| -> io::Result<E::G2Affine> {
            let ptr = &mmap[*offset..*offset + g2_len];
            *offset += g2_len;
            // Safety: this operation is safe, because it's simply
            // casting to a known struct at the correct offset, given
            // the structure of the on-disk data.
            let repr: <E::G2Affine as CurveAffine>::Uncompressed = unsafe {
                *(ptr as *const [u8] as *const <E::G2Affine as CurveAffine>::Uncompressed)
            };

            if checked {
                repr.into_affine()
            } else {
                repr.into_affine_unchecked()
            }
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
            .and_then(|e| {
                if e.is_zero() {
                    Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "point at infinity",
                    ))
                } else {
                    Ok(e)
                }
            })
        };

        let read_length = |mmap: &Mmap, offset: &mut usize| -> Result<usize, std::io::Error> {
            let mut raw_len = &mmap[*offset..*offset + u32_len];
            *offset += u32_len;

            match raw_len.read_u32::<BigEndian>() {
                Ok(len) => Ok(len as usize),
                Err(err) => Err(err),
            }
        };

        let get_g1s = |mmap: &Mmap,
                       offset: &mut usize,
                       param: &mut Vec<E::G1Affine>|
         -> Result<(), std::io::Error> {
            let len = read_length(&mmap, &mut *offset)?;
            for _ in 0..len {
                (*param).push(read_g1(&mmap, &mut *offset)?);
            }

            Ok(())
        };

        let get_g2s = |mmap: &Mmap,
                       offset: &mut usize,
                       param: &mut Vec<E::G2Affine>|
         -> Result<(), std::io::Error> {
            let len = read_length(&mmap, &mut *offset)?;
            for _ in 0..len {
                (*param).push(read_g2(&mmap, &mut *offset)?);
            }

            Ok(())
        };

        let mut offset: usize = 0;
        let vk = VerifyingKey::<E>::read_mmap(&mmap, &mut offset)?;

        let mut h = vec![];
        let mut l = vec![];
        let mut a = vec![];
        let mut b_g1 = vec![];
        let mut b_g2 = vec![];

        get_g1s(&mmap, &mut offset, &mut h)?;
        get_g1s(&mmap, &mut offset, &mut l)?;
        get_g1s(&mmap, &mut offset, &mut a)?;
        get_g1s(&mmap, &mut offset, &mut b_g1)?;
        get_g2s(&mmap, &mut offset, &mut b_g2)?;

        Ok(Parameters {
            vk,
            h: Arc::new(h),
            l: Arc::new(l),
            a: Arc::new(a),
            b_g1: Arc::new(b_g1),
            b_g2: Arc::new(b_g2),
        })
    }

    pub fn read<R: Read>(mut reader: R, checked: bool) -> io::Result<Self> {
        let read_g1 = |reader: &mut R| -> io::Result<E::G1Affine> {
            let mut repr = <E::G1Affine as CurveAffine>::Uncompressed::empty();
            reader.read_exact(repr.as_mut())?;

            if checked {
                repr.into_affine()
            } else {
                repr.into_affine_unchecked()
            }
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
            .and_then(|e| {
                if e.is_zero() {
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
            let mut repr = <E::G2Affine as CurveAffine>::Uncompressed::empty();
            reader.read_exact(repr.as_mut())?;

            if checked {
                repr.into_affine()
            } else {
                repr.into_affine_unchecked()
            }
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
            .and_then(|e| {
                if e.is_zero() {
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

pub struct PreparedVerifyingKey<E: Engine> {
    /// Pairing result of alpha*beta
    alpha_g1_beta_g2: E::Fqk,
    /// -gamma in G2
    neg_gamma_g2: <E::G2Affine as PairingCurveAffine>::Prepared,
    /// -delta in G2
    neg_delta_g2: <E::G2Affine as PairingCurveAffine>::Prepared,
    /// Copy of IC from `VerifiyingKey`.
    ic: Vec<E::G1Affine>,
}

pub struct BatchPreparedVerifyingKey<E: Engine> {
    /// Pairing result of alpha*beta
    alpha_g1_beta_g2: E::Fqk,
    /// gamma in G2
    gamma_g2: <E::G2Affine as PairingCurveAffine>::Prepared,
    /// delta in G2
    delta_g2: <E::G2Affine as PairingCurveAffine>::Prepared,
    /// Copy of IC from `VerifiyingKey`.
    ic: Vec<E::G1Affine>,
}

pub trait ParameterSource<E: Engine>: Send {
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

    use ff::Field;
    use paired::bls12_381::{Bls12, Fr};
    use rand::thread_rng;

    #[test]
    fn serialization() {
        struct MySillyCircuit<E: Engine> {
            a: Option<E::Fr>,
            b: Option<E::Fr>,
        }

        impl<E: Engine> Circuit<E> for MySillyCircuit<E> {
            fn synthesize<CS: ConstraintSystem<E>>(
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

        let rng = &mut thread_rng();

        let params =
            generate_random_parameters::<Bls12, _, _>(MySillyCircuit { a: None, b: None }, rng)
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
            let a = Fr::random(rng);
            let b = Fr::random(rng);
            let mut c = a;
            c.mul_assign(&b);

            let proof = create_random_proof(
                MySillyCircuit {
                    a: Some(a),
                    b: Some(b),
                },
                &params,
                rng,
            )
            .unwrap();

            let mut v = vec![];
            proof.write(&mut v).unwrap();

            assert_eq!(v.len(), 192);

            let de_proof = Proof::read(&v[..]).unwrap();
            assert!(proof == de_proof);

            assert!(verify_proof(&pvk, &proof, &[c]).unwrap());
            assert!(!verify_proof(&pvk, &proof, &[a]).unwrap());
        }
    }
}
