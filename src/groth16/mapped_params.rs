use groupy::{CurveAffine, EncodedPoint};
use paired::Engine;

use crate::SynthesisError;

use memmap::{Mmap, MmapOptions};

use std::fs::File;
use std::io;
use std::marker::PhantomData;
use std::ops::Range;
use std::path::PathBuf;
use std::sync::Arc;

use super::{ParameterSource, VerifyingKey};

#[derive(Clone)]
pub struct MappedParameters<E: Engine> {
    // The parameter file we're reading from.  This is stored so that
    // each (bulk) access can re-map the file, rather than trying to
    // be clever and keeping a persistent memory map around.  This is
    // a much safer way to go (as mmap life-times and consistency
    // guarantees are difficult), and the cost of the mappings should
    // not outweigh the benefits of lazy-loading parameters.
    pub param_file: PathBuf,

    // This is always loaded (i.e. not lazily loaded).
    pub vk: VerifyingKey<E>,

    // Elements of the form ((tau^i * t(tau)) / delta) for i between 0 and
    // m-2 inclusive. Never contains points at infinity.
    pub h: Vec<Range<usize>>,

    // Elements of the form (beta * u_i(tau) + alpha v_i(tau) + w_i(tau)) / delta
    // for all auxiliary inputs. Variables can never be unconstrained, so this
    // never contains points at infinity.
    pub l: Vec<Range<usize>>,

    // QAP "A" polynomials evaluated at tau in the Lagrange basis. Never contains
    // points at infinity: polynomials that evaluate to zero are omitted from
    // the CRS and the prover can deterministically skip their evaluation.
    pub a: Vec<Range<usize>>,

    // QAP "B" polynomials evaluated at tau in the Lagrange basis. Needed in
    // G1 and G2 for C/B queries, respectively. Never contains points at
    // infinity for the same reason as the "A" polynomials.
    pub b_g1: Vec<Range<usize>>,
    pub b_g2: Vec<Range<usize>>,

    pub checked: bool,

    pub _e: PhantomData<E>,
}

unsafe impl<E: Engine> Sync for MappedParameters<E> {}

impl<'a, E: Engine> ParameterSource<E> for &'a MappedParameters<E> {
    type G1Builder = (Arc<Vec<E::G1Affine>>, usize);
    type G2Builder = (Arc<Vec<E::G2Affine>>, usize);

    fn get_vk(&mut self, _: usize) -> Result<VerifyingKey<E>, SynthesisError> {
        Ok(self.vk.clone())
    }

    fn get_h(&mut self, _num_h: usize) -> Result<Self::G1Builder, SynthesisError> {
        let params = File::open(self.param_file.clone())?;
        // Safety: this operation is safe, because we are
        // intentionally memory mapping this file.
        let mmap = unsafe { MmapOptions::new().map(&params)? };

        let mut h = vec![];
        for i in 0..self.h.len() {
            h.push(read_g1::<E>(
                &mmap,
                self.h[i].start,
                self.h[i].end,
                self.checked,
            )?);
        }

        Ok((Arc::new(h), 0))
    }

    fn get_l(&mut self, _num_l: usize) -> Result<Self::G1Builder, SynthesisError> {
        let params = File::open(self.param_file.clone())?;
        // Safety: this operation is safe, because we are
        // intentionally memory mapping this file.
        let mmap = unsafe { MmapOptions::new().map(&params)? };

        let mut l = vec![];
        for i in 0..self.l.len() {
            l.push(read_g1::<E>(
                &mmap,
                self.l[i].start,
                self.l[i].end,
                self.checked,
            )?);
        }

        Ok((Arc::new(l), 0))
    }

    fn get_a(
        &mut self,
        num_inputs: usize,
        _num_a: usize,
    ) -> Result<(Self::G1Builder, Self::G1Builder), SynthesisError> {
        let params = File::open(self.param_file.clone())?;
        // Safety: this operation is safe, because we are
        // intentionally memory mapping this file.
        let mmap = unsafe { MmapOptions::new().map(&params)? };

        let mut a = vec![];
        for i in 0..self.a.len() {
            a.push(read_g1::<E>(
                &mmap,
                self.a[i].start,
                self.a[i].end,
                self.checked,
            )?);
        }

        Ok(((Arc::new(a.clone()), 0), (Arc::new(a), num_inputs)))
    }

    fn get_b_g1(
        &mut self,
        num_inputs: usize,
        _num_b_g1: usize,
    ) -> Result<(Self::G1Builder, Self::G1Builder), SynthesisError> {
        let params = File::open(self.param_file.clone())?;
        // Safety: this operation is safe, because we are
        // intentionally memory mapping this file.
        let mmap = unsafe { MmapOptions::new().map(&params)? };

        let mut b_g1 = vec![];
        for i in 0..self.b_g1.len() {
            b_g1.push(read_g1::<E>(
                &mmap,
                self.b_g1[i].start,
                self.b_g1[i].end,
                self.checked,
            )?);
        }

        Ok(((Arc::new(b_g1.clone()), 0), (Arc::new(b_g1), num_inputs)))
    }

    fn get_b_g2(
        &mut self,
        num_inputs: usize,
        _num_b_g2: usize,
    ) -> Result<(Self::G2Builder, Self::G2Builder), SynthesisError> {
        let params = File::open(self.param_file.clone())?;
        // Safety: this operation is safe, because we are
        // intentionally memory mapping this file.
        let mmap = unsafe { MmapOptions::new().map(&params)? };

        let mut b_g2 = vec![];
        for i in 0..self.b_g2.len() {
            b_g2.push(read_g2::<E>(
                &mmap,
                self.b_g2[i].start,
                self.b_g2[i].end,
                self.checked,
            )?);
        }

        Ok(((Arc::new(b_g2.clone()), 0), (Arc::new(b_g2), num_inputs)))
    }
}

// A re-usable method for parameter loading via mmap.  Unlike the
// internal ones used elsewhere, this one does not update offset state
// and simply does the cast and transform needed.
pub fn read_g1<E: Engine>(
    mmap: &Mmap,
    start: usize,
    end: usize,
    checked: bool,
) -> Result<E::G1Affine, std::io::Error> {
    let ptr = &mmap[start..end];
    // Safety: this operation is safe, because it's simply
    // casting to a known struct at the correct offset, given
    // the structure of the on-disk data.
    let repr =
        unsafe { *(ptr as *const [u8] as *const <E::G1Affine as CurveAffine>::Uncompressed) };

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
}

// A re-usable method for parameter loading via mmap.  Unlike the
// internal ones used elsewhere, this one does not update offset state
// and simply does the cast and transform needed.
pub fn read_g2<E: Engine>(
    mmap: &Mmap,
    start: usize,
    end: usize,
    checked: bool,
) -> Result<E::G2Affine, std::io::Error> {
    let ptr = &mmap[start..end];
    // Safety: this operation is safe, because it's simply
    // casting to a known struct at the correct offset, given
    // the structure of the on-disk data.
    let repr =
        unsafe { *(ptr as *const [u8] as *const <E::G2Affine as CurveAffine>::Uncompressed) };

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
}
