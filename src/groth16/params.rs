use groupy::{CurveAffine, EncodedPoint};
use paired::Engine;

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

use super::{MappedParameters, VerifyingKey};

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
        param_file_path: PathBuf,
        checked: bool,
    ) -> io::Result<MappedParameters<E>> {
        let mut offset: usize = 0;
        let param_file = File::open(&param_file_path)?;
        let params = unsafe { MmapOptions::new().map(&param_file)? };

        let u32_len = mem::size_of::<u32>();
        let g1_len = mem::size_of::<<E::G1Affine as CurveAffine>::Uncompressed>();
        let g2_len = mem::size_of::<<E::G2Affine as CurveAffine>::Uncompressed>();

        let read_length = |params: &Mmap, offset: &mut usize| -> Result<usize, std::io::Error> {
            let mut raw_len = &params[*offset..*offset + u32_len];
            *offset += u32_len;

            match raw_len.read_u32::<BigEndian>() {
                Ok(len) => Ok(len as usize),
                Err(err) => Err(err),
            }
        };

        let get_offsets = |params: &Mmap,
                           offset: &mut usize,
                           param: &mut Vec<Range<usize>>,
                           range_len: usize|
         -> Result<(), std::io::Error> {
            let len = read_length(&params, &mut *offset)?;
            for _ in 0..len {
                (*param).push(Range {
                    start: *offset,
                    end: *offset + range_len,
                });
                *offset += range_len;
            }

            Ok(())
        };

        let vk = VerifyingKey::<E>::read_mmap(&params, &mut offset)?;

        let mut h = vec![];
        let mut l = vec![];
        let mut a = vec![];
        let mut b_g1 = vec![];
        let mut b_g2 = vec![];

        get_offsets(&params, &mut offset, &mut h, g1_len)?;
        get_offsets(&params, &mut offset, &mut l, g1_len)?;
        get_offsets(&params, &mut offset, &mut a, g1_len)?;
        get_offsets(&params, &mut offset, &mut b_g1, g1_len)?;
        get_offsets(&params, &mut offset, &mut b_g2, g2_len)?;

        Ok(MappedParameters {
            param_file_path,
            param_file,
            params,
            vk,
            h,
            l,
            a,
            b_g1,
            b_g2,
            checked,
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

pub trait ParameterSource<E: Engine>: Send + Sync {
    type G1Builder: SourceBuilder<E::G1Affine>;
    type G2Builder: SourceBuilder<E::G2Affine>;

    fn get_vk(&self, num_ic: usize) -> Result<&VerifyingKey<E>, SynthesisError>;
    fn get_h(&self, num_h: usize) -> Result<Self::G1Builder, SynthesisError>;
    fn get_l(&self, num_l: usize) -> Result<Self::G1Builder, SynthesisError>;
    fn get_a(
        &self,
        num_inputs: usize,
        num_aux: usize,
    ) -> Result<(Self::G1Builder, Self::G1Builder), SynthesisError>;
    fn get_b_g1(
        &self,
        num_inputs: usize,
        num_aux: usize,
    ) -> Result<(Self::G1Builder, Self::G1Builder), SynthesisError>;
    fn get_b_g2(
        &self,
        num_inputs: usize,
        num_aux: usize,
    ) -> Result<(Self::G2Builder, Self::G2Builder), SynthesisError>;
}

impl<'a, E: Engine> ParameterSource<E> for &'a Parameters<E> {
    type G1Builder = (Arc<Vec<E::G1Affine>>, usize);
    type G2Builder = (Arc<Vec<E::G2Affine>>, usize);

    fn get_vk(&self, _: usize) -> Result<&VerifyingKey<E>, SynthesisError> {
        Ok(&self.vk)
    }

    fn get_h(&self, _: usize) -> Result<Self::G1Builder, SynthesisError> {
        Ok((self.h.clone(), 0))
    }

    fn get_l(&self, _: usize) -> Result<Self::G1Builder, SynthesisError> {
        Ok((self.l.clone(), 0))
    }

    fn get_a(
        &self,
        num_inputs: usize,
        _: usize,
    ) -> Result<(Self::G1Builder, Self::G1Builder), SynthesisError> {
        Ok(((self.a.clone(), 0), (self.a.clone(), num_inputs)))
    }

    fn get_b_g1(
        &self,
        num_inputs: usize,
        _: usize,
    ) -> Result<(Self::G1Builder, Self::G1Builder), SynthesisError> {
        Ok(((self.b_g1.clone(), 0), (self.b_g1.clone(), num_inputs)))
    }

    fn get_b_g2(
        &self,
        num_inputs: usize,
        _: usize,
    ) -> Result<(Self::G2Builder, Self::G2Builder), SynthesisError> {
        Ok(((self.b_g2.clone(), 0), (self.b_g2.clone(), num_inputs)))
    }
}
