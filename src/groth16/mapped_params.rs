use groupy::{CurveAffine, EncodedPoint};
use paired::Engine;

use crate::SynthesisError;

use memmap::Mmap;

use std::fs::File;
use std::io;
use std::ops::Range;
use std::path::PathBuf;
use std::sync::Arc;

use super::{ParameterSource, VerifyingKey};

pub struct MappedParameters<E: Engine> {
    /// The parameter file we're reading from.  
    pub param_file_path: PathBuf,
    /// The file descriptor we have mmaped.
    pub param_file: File,
    /// The actual mmap.
    pub params: Mmap,

    /// This is always loaded (i.e. not lazily loaded).
    pub vk: VerifyingKey<E>,

    /// Elements of the form ((tau^i * t(tau)) / delta) for i between 0 and
    /// m-2 inclusive. Never contains points at infinity.
    pub h: Vec<Range<usize>>,

    /// Elements of the form (beta * u_i(tau) + alpha v_i(tau) + w_i(tau)) / delta
    /// for all auxiliary inputs. Variables can never be unconstrained, so this
    /// never contains points at infinity.
    pub l: Vec<Range<usize>>,

    /// QAP "A" polynomials evaluated at tau in the Lagrange basis. Never contains
    /// points at infinity: polynomials that evaluate to zero are omitted from
    /// the CRS and the prover can deterministically skip their evaluation.
    pub a: Vec<Range<usize>>,

    /// QAP "B" polynomials evaluated at tau in the Lagrange basis. Needed in
    /// G1 and G2 for C/B queries, respectively. Never contains points at
    /// infinity for the same reason as the "A" polynomials.
    pub b_g1: Vec<Range<usize>>,
    pub b_g2: Vec<Range<usize>>,

    pub checked: bool,
}

impl<'a, E: Engine> ParameterSource<E> for &'a MappedParameters<E> {
    type G1Builder = (Arc<Vec<E::G1Affine>>, usize);
    type G2Builder = (Arc<Vec<E::G2Affine>>, usize);

    fn get_vk(&self, _: usize) -> Result<&VerifyingKey<E>, SynthesisError> {
        Ok(&self.vk)
    }

    fn get_h(&self, _num_h: usize) -> Result<Self::G1Builder, SynthesisError> {
        let builder = self
            .h
            .iter()
            .cloned()
            .map(|h| read_g1::<E>(&self.params, h, self.checked))
            .collect::<Result<_, _>>()?;

        Ok((Arc::new(builder), 0))
    }

    fn get_l(&self, _num_l: usize) -> Result<Self::G1Builder, SynthesisError> {
        let builder = self
            .l
            .iter()
            .cloned()
            .map(|l| read_g1::<E>(&self.params, l, self.checked))
            .collect::<Result<_, _>>()?;

        Ok((Arc::new(builder), 0))
    }

    fn get_a(
        &self,
        num_inputs: usize,
        _num_a: usize,
    ) -> Result<(Self::G1Builder, Self::G1Builder), SynthesisError> {
        let builder = self
            .a
            .iter()
            .cloned()
            .map(|a| read_g1::<E>(&self.params, a, self.checked))
            .collect::<Result<_, _>>()?;

        let builder: Arc<Vec<_>> = Arc::new(builder);

        Ok(((builder.clone(), 0), (builder, num_inputs)))
    }

    fn get_b_g1(
        &self,
        num_inputs: usize,
        _num_b_g1: usize,
    ) -> Result<(Self::G1Builder, Self::G1Builder), SynthesisError> {
        let builder = self
            .b_g1
            .iter()
            .cloned()
            .map(|b_g1| read_g1::<E>(&self.params, b_g1, self.checked))
            .collect::<Result<_, _>>()?;

        let builder: Arc<Vec<_>> = Arc::new(builder);

        Ok(((builder.clone(), 0), (builder, num_inputs)))
    }

    fn get_b_g2(
        &self,
        num_inputs: usize,
        _num_b_g2: usize,
    ) -> Result<(Self::G2Builder, Self::G2Builder), SynthesisError> {
        let builder = self
            .b_g2
            .iter()
            .cloned()
            .map(|b_g2| read_g2::<E>(&self.params, b_g2, self.checked))
            .collect::<Result<_, _>>()?;

        let builder: Arc<Vec<_>> = Arc::new(builder);

        Ok(((builder.clone(), 0), (builder, num_inputs)))
    }
}

// A re-usable method for parameter loading via mmap.  Unlike the
// internal ones used elsewhere, this one does not update offset state
// and simply does the cast and transform needed.
pub fn read_g1<E: Engine>(
    mmap: &Mmap,
    range: Range<usize>,
    checked: bool,
) -> Result<E::G1Affine, std::io::Error> {
    let ptr = &mmap[range];
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
    range: Range<usize>,
    checked: bool,
) -> Result<E::G2Affine, std::io::Error> {
    let ptr = &mmap[range];
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
