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
    pub fn create(_: bool) -> GPUResult<FFTKernel<E>> {
        return Err(GPUError::GPUDisabled);
    }

    pub fn radix_fft(&mut self, _: &mut [E::Fr], _: &E::Fr, _: u32) -> GPUResult<()> {
        return Err(GPUError::GPUDisabled);
    }
}

pub struct MultiexpKernel<E>(PhantomData<E>)
where
    E: ScalarEngine;

impl<E> MultiexpKernel<E>
where
    E: ScalarEngine,
{
    pub fn create(_: bool) -> GPUResult<MultiexpKernel<E>> {
        return Err(GPUError::GPUDisabled);
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
        return Err(GPUError::GPUDisabled);
    }
}

use paired::Engine;

macro_rules! locked_kernel {
    ($class:ident) => {
        pub struct $class<E>(PhantomData<E>);

        impl<E> $class<E>
        where
            E: Engine,
        {
            pub fn new(_: usize, _: bool) -> $class<E> {
                $class::<E>(PhantomData)
            }

            pub fn with<F, R, K>(&mut self, _: F) -> GPUResult<R>
            where
                F: FnMut(&mut K) -> GPUResult<R>,
            {
                return Err(GPUError::GPUDisabled);
            }
        }
    };
}

locked_kernel!(LockedFFTKernel);
locked_kernel!(LockedMultiexpKernel);
