use ff::PrimeField;
use groupy::{CurveAffine, CurveProjective};
use ocl::traits::OclPrm;

// Everything that needs to be copied to GPU needs to implement OclPrm trait.
// This module implements a generic OclPrm version of PrimeField, CurveAffine and CurveProjective
// so that they can be copied to GPU.
// A transmute from [PrimeField] to [PrimeFieldStruct] is safe as their sizes are equal.
// Also safe for [CurveAffine] to [CurveAffineStruct] and [CurveProjective] to [CurveProjectiveStruct]
// It costs less memory to just transmute the data sources for both FFT and Multiexp to their
// OpenCL friendly equivalents instead of mapping them to a new array with each element casted.

#[derive(PartialEq, Debug, Clone, Copy)]
#[repr(transparent)]
pub struct PrimeFieldStruct<T>(pub T);
impl<T> Default for PrimeFieldStruct<T>
where
    T: PrimeField,
{
    fn default() -> Self {
        PrimeFieldStruct::<T>(T::zero())
    }
}
unsafe impl<T> OclPrm for PrimeFieldStruct<T> where T: PrimeField {}

#[derive(PartialEq, Debug, Clone, Copy)]
#[repr(transparent)]
pub struct CurveAffineStruct<T>(pub T);
impl<T> Default for CurveAffineStruct<T>
where
    T: CurveAffine,
{
    fn default() -> Self {
        CurveAffineStruct::<T>(T::zero())
    }
}
unsafe impl<T> OclPrm for CurveAffineStruct<T> where T: CurveAffine {}

#[derive(PartialEq, Debug, Clone, Copy)]
#[repr(transparent)]
pub struct CurveProjectiveStruct<T>(pub T);
impl<T> Default for CurveProjectiveStruct<T>
where
    T: CurveProjective,
{
    fn default() -> Self {
        CurveProjectiveStruct::<T>(T::zero())
    }
}
unsafe impl<T> OclPrm for CurveProjectiveStruct<T> where T: CurveProjective {}
