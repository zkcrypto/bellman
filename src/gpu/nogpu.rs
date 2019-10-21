use ff::{PrimeField, ScalarEngine};
use std::sync::Arc;
use std::marker::PhantomData;
use paired::{Engine, CurveAffine};
use super::error::{GPUResult, GPUError};

// This module is compiled instead of `fft.rs` and `multiexp.rs` if `gpu` feature is disabled.

pub struct FFTKernel<F>(PhantomData::<F>) where F: PrimeField;

impl<F> FFTKernel<F> where F: PrimeField {

    pub fn create(_: u32) -> GPUResult<FFTKernel::<F>> {
        return Err(GPUError {msg: "GPU accelerator is not enabled!".to_string()});
    }

    pub fn radix_fft(&mut self, _: &mut [F], _: &F, _: u32) -> GPUResult<()> {
        return Err(GPUError {msg: "GPU accelerator is not enabled!".to_string()});
    }

    pub fn mul_by_field(&mut self, _: &mut [F], _: &F, _: u32) -> GPUResult<()> {
        return Err(GPUError {msg: "GPU accelerator is not enabled!".to_string()});
    }
}

pub struct MultiexpKernel<E>(PhantomData::<E>) where E: Engine;

impl<E> MultiexpKernel<E> where E: Engine {

    pub fn create() -> GPUResult<MultiexpKernel<E>> {
        return Err(GPUError {msg: "GPU accelerator is not enabled!".to_string()});
    }

    pub fn multiexp<G>(&mut self,
            _: Arc<Vec<G>>,
            _: Arc<Vec<<<G::Engine as ScalarEngine>::Fr as PrimeField>::Repr>>,
            _: usize,
            _: usize)
            -> GPUResult<(<G as CurveAffine>::Projective)>
            where G: CurveAffine {
        return Err(GPUError {msg: "GPU accelerator is not enabled!".to_string()});
    }
}
