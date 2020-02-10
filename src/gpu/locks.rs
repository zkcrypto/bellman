use fs2::FileExt;
use log::{debug, info, warn};
use std::fs::File;
use std::path::PathBuf;

const GPU_LOCK_NAME: &str = "bellman.gpu.lock";
const PRIORITY_LOCK_NAME: &str = "bellman.priority.lock";
fn tmp_path(filename: &str) -> PathBuf {
    let mut p = std::env::temp_dir();
    p.push(filename);
    p
}

/// `GPULock` prevents two kernel objects to be instantiated simultaneously.
#[derive(Debug)]
pub struct GPULock(File);
impl GPULock {
    pub fn lock() -> GPULock {
        debug!("Acquiring GPU lock...");
        let f = File::create(tmp_path(GPU_LOCK_NAME)).unwrap();
        f.lock_exclusive().unwrap();
        debug!("GPU lock acquired!");
        GPULock(f)
    }
}
impl Drop for GPULock {
    fn drop(&mut self) {
        debug!("GPU lock released!");
    }
}

/// `PrioriyLock` is like a flag. When acquired, it means a high-priority process
/// needs to acquire the GPU really soon. Acquiring the `PriorityLock` is like
/// signaling all other processes to release their `GPULock`s.
/// Only one process can have the `PriorityLock` at a time.
#[derive(Debug)]
pub struct PriorityLock(File);
impl PriorityLock {
    pub fn lock() -> PriorityLock {
        debug!("Acquiring priority lock...");
        let f = File::create(tmp_path(PRIORITY_LOCK_NAME)).unwrap();
        f.lock_exclusive().unwrap();
        debug!("Priority lock acquired!");
        PriorityLock(f)
    }
    pub fn is_locked() -> bool {
        File::create(tmp_path(PRIORITY_LOCK_NAME))
            .unwrap()
            .try_lock_exclusive()
            .is_err()
    }
}
impl Drop for PriorityLock {
    fn drop(&mut self) {
        debug!("Priority lock released!");
    }
}

pub struct LockedKernel<K, F>
where
    F: Fn() -> Option<K>,
{
    priority: bool,
    _f: F,
    kernel: Option<K>,
}

impl<K, F> LockedKernel<K, F>
where
    F: Fn() -> Option<K>,
{
    pub fn new(f: F, priority: bool) -> LockedKernel<K, F> {
        LockedKernel::<K, F> {
            priority,
            _f: f,
            kernel: None,
        }
    }
    pub fn get(&mut self) -> &mut Option<K> {
        if !self.priority && PriorityLock::is_locked() {
            if let Some(_kernel) = self.kernel.take() {
                warn!("GPU acquired by a high priority process! Freeing up kernels...");
            }
        } else if self.kernel.is_none() {
            info!("GPU is available!");
            self.kernel = (self._f)();
        }
        &mut self.kernel
    }
}
