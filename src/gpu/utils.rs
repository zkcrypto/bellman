use ocl::{Device, Platform};
use super::error::{GPUResult, GPUError};
use std::env;

pub const GPU_NVIDIA_PLATFORM_NAME : &str = "NVIDIA CUDA";
pub const CPU_INTEL_PLATFORM_NAME : &str = "Intel(R) CPU Runtime for OpenCL(TM) Applications";

pub fn get_devices(platform_name: &str) -> GPUResult<Vec<Device>> {

    if env::var("BELLMAN_NO_GPU").is_ok() {
        return Err(GPUError {msg: "GPU accelerator is disabled!".to_string()})
    }

    let platform = Platform::list()?.into_iter().find(|&p|
        match p.name() {
            Ok(p) => p == platform_name,
            Err(_) => false
        });
    match platform {
        Some(p) => Ok(Device::list_all(p)?),
        None => Err(GPUError {msg: "GPU platform not found!".to_string() })
    }
}

use std::collections::HashMap;
lazy_static!{
    static ref CORE_COUNTS: HashMap<&'static str, usize> = vec![
        ("GeForce RTX 2080 Ti", 4352),
        ("GeForce RTX 2080 SUPER", 3072),
        ("GeForce RTX 2080", 2944),
        ("GeForce GTX 1080 Ti", 3584),
        ("GeForce GTX 1080", 2560),
        ("GeForce GTX 1060", 1280),
    ].into_iter().collect();
}

pub fn get_core_count(d: Device) -> GPUResult<usize> {
    match CORE_COUNTS.get(&d.name()?[..]) {
        Some(&cores) => Ok(cores),
        None => Err(GPUError {msg: "Device unknown!".to_string() })
    }
}