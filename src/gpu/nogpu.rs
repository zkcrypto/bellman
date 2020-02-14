use super::error::{GPUError, GPUResult};
use crate::multicore::Worker;
use ff::{PrimeField, ScalarEngine};
use groupy::CurveAffine;
use std::marker::PhantomData;
use std::sync::Arc;

// This module is compiled instead of `fft.rs` and `multiexp.rs` if `gpu` feature is disabled.

pub struct FFTKernel<E>(PhantomData<E>)
where
    E: ScalarEngine;

impl<E> FFTKernel<E>
where
    E: ScalarEngine,
{
    pub fn create(_: u32) -> GPUResult<FFTKernel<E>> {
        return Err(GPUError::Simple("GPU accelerator is not enabled!"));
    }

    pub fn radix_fft(&mut self, _: &mut [E::Fr], _: &E::Fr, _: u32) -> GPUResult<()> {
        return Err(GPUError::Simple("GPU accelerator is not enabled!"));
    }
}

pub struct MultiexpKernel<E>(PhantomData<E>)
where
    E: ScalarEngine;

impl<E> MultiexpKernel<E>
where
    E: ScalarEngine,
{
    pub fn create() -> GPUResult<MultiexpKernel<E>> {
        return Err(GPUError::Simple("GPU accelerator is not enabled!"));
    }

    pub fn multiexp<G>(
        &mut self,
        _: &Worker,
        _: Arc<Vec<G>>,
        _: Arc<Vec<<<G::Engine as ScalarEngine>::Fr as PrimeField>::Repr>>,
        _: usize,
        _: usize,
    ) -> GPUResult<<G as CurveAffine>::Projective>
    where
        G: CurveAffine,
    {
        return Err(GPUError::Simple("GPU accelerator is not enabled!"));
    }
}

pub struct LockedKernel<K> {
    kernel: Option<K>,
}

impl<K> LockedKernel<K> {
    pub fn new<F>(_: F, _: bool) -> LockedKernel<K> {
        LockedKernel { kernel: None }
    }
    pub fn get(&mut self) -> &mut Option<K> {
        &mut self.kernel
    }
}
