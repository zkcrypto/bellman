use super::error::{GPUError, GPUResult};
use super::locks;
use super::sources;
use super::structs;
use super::utils;
use super::GPU_NVIDIA_DEVICES;
use crate::multicore::Worker;
use crate::multiexp::{multiexp as cpu_multiexp, FullDensity};
use crossbeam::thread;
use ff::{PrimeField, ScalarEngine};
use futures::Future;
use groupy::{CurveAffine, CurveProjective};
use log::{error, info};
use ocl::{Buffer, Device, MemFlags, ProQue};
use paired::Engine;
use std::sync::Arc;

// NOTE: Please read `structs.rs` for an explanation for unsafe transmutes of this code!

const MAX_WINDOW_SIZE: usize = 10;
const LOCAL_WORK_SIZE: usize = 256;
const MEMORY_PADDING: f64 = 0.2f64; // Let 20% of GPU memory be free

pub fn get_cpu_utilization() -> f64 {
    use std::env;
    env::var("BELLMAN_CPU_UTILIZATION")
        .and_then(|v| match v.parse() {
            Ok(val) => Ok(val),
            Err(_) => {
                error!("Invalid BELLMAN_CPU_UTILIZATION! Defaulting to 0...");
                Ok(0f64)
            }
        })
        .unwrap_or(0f64)
        .max(0f64)
        .min(1f64)
}

// Multiexp kernel for a single GPU
pub struct SingleMultiexpKernel<E>
where
    E: Engine,
{
    proque: ProQue,

    g1_base_buffer: Buffer<structs::CurveAffineStruct<E::G1Affine>>,
    g1_bucket_buffer: Buffer<structs::CurveProjectiveStruct<E::G1>>,
    g1_result_buffer: Buffer<structs::CurveProjectiveStruct<E::G1>>,

    g2_base_buffer: Buffer<structs::CurveAffineStruct<E::G2Affine>>,
    g2_bucket_buffer: Buffer<structs::CurveProjectiveStruct<E::G2>>,
    g2_result_buffer: Buffer<structs::CurveProjectiveStruct<E::G2>>,

    exp_buffer: Buffer<structs::PrimeFieldStruct<E::Fr>>,

    core_count: usize,
    n: usize,

    priority: bool,
}

fn calc_num_groups(core_count: usize, num_windows: usize) -> usize {
    // Observations show that we get the best performance when num_groups * num_windows ~= 2 * CUDA_CORES
    return 2 * core_count / num_windows;
}

fn calc_window_size(n: usize, exp_bits: usize, core_count: usize) -> usize {
    // window_size = ln(n / num_groups)
    // num_windows = exp_bits / window_size
    // num_groups = 2 * core_count / num_windows = 2 * core_count * window_size / exp_bits
    // window_size = ln(n / num_groups) = ln(n * exp_bits / (2 * core_count * window_size))
    // window_size = ln(exp_bits * n / (2 * core_count)) - ln(window_size)
    //
    // Thus we need to solve the following equation:
    // window_size + ln(window_size) = ln(exp_bits * n / (2 * core_count))
    let lower_bound = (((exp_bits * n) as f64) / ((2 * core_count) as f64)).ln();
    for w in 0..MAX_WINDOW_SIZE {
        if (w as f64) + (w as f64).ln() > lower_bound {
            return w;
        }
    }
    return MAX_WINDOW_SIZE;
}

fn calc_best_chunk_size(max_window_size: usize, core_count: usize, exp_bits: usize) -> usize {
    // Best chunk-size (N) can also be calculated using the same logic as calc_window_size:
    // n = e^window_size * window_size * 2 * core_count / exp_bits
    (((max_window_size as f64).exp() as f64)
        * (max_window_size as f64)
        * 2f64
        * (core_count as f64)
        / (exp_bits as f64))
        .ceil() as usize
}

fn calc_chunk_size<E>(mem: u64, core_count: usize) -> usize
where
    E: Engine,
{
    let aff_size = std::mem::size_of::<E::G1Affine>() + std::mem::size_of::<E::G2Affine>();
    let exp_size = std::mem::size_of::<E::Fr>();
    let proj_size = std::mem::size_of::<E::G1>() + std::mem::size_of::<E::G2>();
    ((((mem as f64) * (1f64 - MEMORY_PADDING)) as usize)
        - (2 * core_count * ((1 << MAX_WINDOW_SIZE) + 1) * proj_size))
        / (aff_size + exp_size)
}

impl<E> SingleMultiexpKernel<E>
where
    E: Engine,
{
    pub fn create(d: Device, priority: bool) -> GPUResult<SingleMultiexpKernel<E>> {
        let src = sources::kernel::<E>();
        let pq = ProQue::builder().device(d).src(src).dims(1).build()?;

        let exp_bits = std::mem::size_of::<E::Fr>() * 8;
        let core_count = utils::get_core_count(d)?;
        let mem = utils::get_memory(d)?;
        let max_n = calc_chunk_size::<E>(mem, core_count);
        let best_n = calc_best_chunk_size(MAX_WINDOW_SIZE, core_count, exp_bits);
        let n = std::cmp::min(max_n, best_n);
        let max_bucket_len = 1 << MAX_WINDOW_SIZE;

        // Each group will have `num_windows` threads and as there are `num_groups` groups, there will
        // be `num_groups` * `num_windows` threads in total.
        // Each thread will use `num_groups` * `num_windows` * `bucket_len` buckets.

        let g1basebuff = Buffer::builder()
            .queue(pq.queue().clone())
            .flags(MemFlags::new().read_write())
            .len(n)
            .build()?;
        let g1buckbuff = Buffer::builder()
            .queue(pq.queue().clone())
            .flags(MemFlags::new().read_write())
            .len(2 * core_count * max_bucket_len)
            .build()?;
        let g1resbuff = Buffer::builder()
            .queue(pq.queue().clone())
            .flags(MemFlags::new().read_write())
            .len(2 * core_count)
            .build()?;

        let g2basebuff = Buffer::builder()
            .queue(pq.queue().clone())
            .flags(MemFlags::new().read_write())
            .len(n)
            .build()?;
        let g2buckbuff = Buffer::builder()
            .queue(pq.queue().clone())
            .flags(MemFlags::new().read_write())
            .len(2 * core_count * max_bucket_len)
            .build()?;
        let g2resbuff = Buffer::builder()
            .queue(pq.queue().clone())
            .flags(MemFlags::new().read_write())
            .len(2 * core_count)
            .build()?;

        let expbuff = Buffer::builder()
            .queue(pq.queue().clone())
            .flags(MemFlags::new().read_write())
            .len(n)
            .build()?;

        Ok(SingleMultiexpKernel {
            proque: pq,
            g1_base_buffer: g1basebuff,
            g1_bucket_buffer: g1buckbuff,
            g1_result_buffer: g1resbuff,
            g2_base_buffer: g2basebuff,
            g2_bucket_buffer: g2buckbuff,
            g2_result_buffer: g2resbuff,
            exp_buffer: expbuff,
            core_count: core_count,
            n,
            priority,
        })
    }

    pub fn multiexp<G>(
        &mut self,
        bases: &[G],
        exps: &[<<G::Engine as ScalarEngine>::Fr as PrimeField>::Repr],
        n: usize,
    ) -> GPUResult<<G as CurveAffine>::Projective>
    where
        G: CurveAffine,
    {
        if locks::PriorityLock::should_break(self.priority) {
            return Err(GPUError::GPUTaken);
        }

        let exp_bits = std::mem::size_of::<E::Fr>() * 8;
        let window_size = calc_window_size(n as usize, exp_bits, self.core_count);
        let num_windows = ((exp_bits as f64) / (window_size as f64)).ceil() as usize;
        let num_groups = calc_num_groups(self.core_count, num_windows);

        let mut res = vec![<G as CurveAffine>::Projective::zero(); num_groups * num_windows];
        let texps = unsafe {
            std::mem::transmute::<
                &[<<G::Engine as ScalarEngine>::Fr as PrimeField>::Repr],
                &[structs::PrimeFieldStruct<E::Fr>],
            >(exps)
        };
        self.exp_buffer.write(texps).enq()?;

        // Make global work size divisible by `LOCAL_WORK_SIZE`
        let mut gws = num_windows * num_groups;
        gws += (LOCAL_WORK_SIZE - (gws % LOCAL_WORK_SIZE)) % LOCAL_WORK_SIZE;

        let sz = std::mem::size_of::<G>(); // Trick, used for dispatching between G1 and G2!
        if sz == std::mem::size_of::<E::G1Affine>() {
            let tbases = unsafe {
                &*(bases as *const [G]
                    as *const [structs::CurveAffineStruct<<E as Engine>::G1Affine>])
            };
            self.g1_base_buffer.write(tbases).enq()?;
            let kernel = self
                .proque
                .kernel_builder("G1_bellman_multiexp")
                .global_work_size([gws])
                .arg(&self.g1_base_buffer)
                .arg(&self.g1_bucket_buffer)
                .arg(&self.g1_result_buffer)
                .arg(&self.exp_buffer)
                .arg(n as u32)
                .arg(num_groups as u32)
                .arg(num_windows as u32)
                .arg(window_size as u32)
                .build()?;
            unsafe {
                kernel.enq()?;
            }
            let tres = unsafe {
                &mut *(&mut res as *mut Vec<<G as CurveAffine>::Projective>
                    as *mut Vec<structs::CurveProjectiveStruct<<E as Engine>::G1>>)
            };
            self.g1_result_buffer.read(tres).enq()?;
        } else if sz == std::mem::size_of::<E::G2Affine>() {
            let tbases = unsafe {
                &*(bases as *const [G]
                    as *const [structs::CurveAffineStruct<<E as Engine>::G2Affine>])
            };
            self.g2_base_buffer.write(tbases).enq()?;
            let kernel = self
                .proque
                .kernel_builder("G2_bellman_multiexp")
                .global_work_size([gws])
                .arg(&self.g2_base_buffer)
                .arg(&self.g2_bucket_buffer)
                .arg(&self.g2_result_buffer)
                .arg(&self.exp_buffer)
                .arg(n as u32)
                .arg(num_groups as u32)
                .arg(num_windows as u32)
                .arg(window_size as u32)
                .build()?;
            unsafe {
                kernel.enq()?;
            }
            let tres = unsafe {
                &mut *(&mut res as *mut Vec<<G as CurveAffine>::Projective>
                    as *mut Vec<structs::CurveProjectiveStruct<<E as Engine>::G2>>)
            };
            self.g2_result_buffer.read(tres).enq()?;
        } else {
            return Err(GPUError::Simple("Only E::G1 and E::G2 are supported!"));
        }

        // Using the algorithm below, we can calculate the final result by accumulating the results
        // of those `NUM_GROUPS` * `NUM_WINDOWS` threads.
        let mut acc = <G as CurveAffine>::Projective::zero();
        let mut bits = 0;
        for i in 0..num_windows {
            let w = std::cmp::min(window_size, exp_bits - bits);
            for _ in 0..w {
                acc.double();
            }
            for g in 0..num_groups {
                acc.add_assign(&res[g * num_windows + i]);
            }
            bits += w; // Process the next window
        }

        Ok(acc)
    }
}

// A struct that containts several multiexp kernels for different devices
pub struct MultiexpKernel<E>
where
    E: Engine,
{
    kernels: Vec<SingleMultiexpKernel<E>>,
    _lock: locks::GPULock, // RFC 1857: struct fields are dropped in the same order as they are declared.
}

impl<E> MultiexpKernel<E>
where
    E: Engine,
{
    pub fn create(priority: bool) -> GPUResult<MultiexpKernel<E>> {
        let lock = locks::GPULock::lock();

        let kernels: Vec<_> = GPU_NVIDIA_DEVICES
            .iter()
            .map(|d| SingleMultiexpKernel::<E>::create(*d, priority))
            .filter(|res| res.is_ok())
            .map(|res| res.unwrap())
            .collect();
        if kernels.is_empty() {
            return Err(GPUError::Simple("No working GPUs found!"));
        }
        info!(
            "Multiexp: {} working device(s) selected. (CPU utilization: {})",
            kernels.len(),
            get_cpu_utilization()
        );
        for (i, k) in kernels.iter().enumerate() {
            info!(
                "Multiexp: Device {}: {} (Chunk-size: {})",
                i,
                k.proque.device().name()?,
                k.n
            );
        }
        return Ok(MultiexpKernel::<E> {
            kernels,
            _lock: lock,
        });
    }

    pub fn multiexp<G>(
        &mut self,
        pool: &Worker,
        bases: Arc<Vec<G>>,
        exps: Arc<Vec<<<G::Engine as ScalarEngine>::Fr as PrimeField>::Repr>>,
        skip: usize,
        n: usize,
    ) -> GPUResult<<G as CurveAffine>::Projective>
    where
        G: CurveAffine,
        <G as groupy::CurveAffine>::Engine: paired::Engine,
    {
        let num_devices = self.kernels.len();
        // Bases are skipped by `self.1` elements, when converted from (Arc<Vec<G>>, usize) to Source
        // https://github.com/zkcrypto/bellman/blob/10c5010fd9c2ca69442dc9775ea271e286e776d8/src/multiexp.rs#L38
        let bases = &bases[skip..(skip + n)];
        let exps = &exps[..n];

        let cpu_n = ((n as f64) * get_cpu_utilization()) as usize;
        let n = n - cpu_n;
        let (cpu_bases, bases) = bases.split_at(cpu_n);
        let (cpu_exps, exps) = exps.split_at(cpu_n);

        let chunk_size = ((n as f64) / (num_devices as f64)).ceil() as usize;

        match thread::scope(|s| -> Result<<G as CurveAffine>::Projective, GPUError> {
            let mut acc = <G as CurveAffine>::Projective::zero();
            let mut threads = Vec::new();
            if n > 0 {
                for ((bases, exps), kern) in bases
                    .chunks(chunk_size)
                    .zip(exps.chunks(chunk_size))
                    .zip(self.kernels.iter_mut())
                {
                    threads.push(s.spawn(
                        move |_| -> Result<<G as CurveAffine>::Projective, GPUError> {
                            let mut acc = <G as CurveAffine>::Projective::zero();
                            for (bases, exps) in bases.chunks(kern.n).zip(exps.chunks(kern.n)) {
                                let result = kern.multiexp(bases, exps, bases.len())?;
                                acc.add_assign(&result);
                            }
                            Ok(acc)
                        },
                    ));
                }
            }

            let cpu_acc = cpu_multiexp(
                &pool,
                (Arc::new(cpu_bases.to_vec()), 0),
                FullDensity,
                Arc::new(cpu_exps.to_vec()),
                &mut None,
            );

            let mut results = vec![];
            for t in threads {
                results.push(t.join());
            }
            for r in results {
                acc.add_assign(&r??);
            }

            acc.add_assign(&cpu_acc.wait().unwrap());

            Ok(acc)
        }) {
            Ok(res) => res,
            Err(e) => Err(GPUError::from(e)),
        }
    }
}
