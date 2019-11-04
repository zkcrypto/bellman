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

lazy_static! {
    pub static ref GPU_NVIDIA_DEVICES: Vec<Device> = {
        get_devices(GPU_NVIDIA_PLATFORM_NAME).unwrap_or(Vec::new())
    };
}
