use ocl::{Device, Platform};
use std::panic;
use super::error::{GPUResult, GPUError};

pub const GPU_NVIDIA_PLATFORM_NAME : &str = "NVIDIA CUDA";
pub const CPU_INTEL_PLATFORM_NAME : &str = "Intel(R) CPU Runtime for OpenCL(TM) Applications";

pub fn get_devices(platform_name: &str) -> GPUResult<Vec<Device>> {
    match panic::catch_unwind(|| {
        let platform = Platform::list().into_iter().find(|&p|
            match p.name() {
                Ok(p) => p == platform_name,
                Err(_) => false
            });
        Device::list_all(platform.unwrap()).unwrap()
    }) {
        Ok(devs) => Ok(devs),
        Err(_) => Err(GPUError {msg: "GPU platform not found!".to_string()})
    }
}

lazy_static! {
    pub static ref GPU_NVIDIA_DEVICES: Vec<Device> = {
        get_devices(GPU_NVIDIA_PLATFORM_NAME).unwrap_or(Vec::new())
    };
}
