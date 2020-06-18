use crate::gpu::error::{GPUError, GPUResult};
use ocl::{Device, Platform};

use log::{info, warn};
use std::collections::HashMap;
use std::env;

pub const GPU_NVIDIA_PLATFORM_NAME: &str = "NVIDIA CUDA";
// pub const CPU_INTEL_PLATFORM_NAME: &str = "Intel(R) CPU Runtime for OpenCL(TM) Applications";

pub fn get_devices(platform_name: &str) -> GPUResult<Vec<Device>> {
    if env::var("BELLMAN_NO_GPU").is_ok() {
        return Err(GPUError::Simple("GPU accelerator is disabled!"));
    }

    let platform = Platform::list()?.into_iter().find(|&p| match p.name() {
        Ok(p) => p == platform_name,
        Err(_) => false,
    });
    match platform {
        Some(p) => Ok(Device::list_all(p)?),
        None => Err(GPUError::Simple("GPU platform not found!")),
    }
}

lazy_static::lazy_static! {
    static ref CORE_COUNTS: HashMap<String, usize> = {
        let mut core_counts : HashMap<String, usize> = vec![
            ("Quadro RTX 6000".to_string(), 4608),

            ("TITAN RTX".to_string(), 4608),

            ("Tesla V100".to_string(), 5120),
            ("Tesla P100".to_string(), 3584),
            ("Tesla T4".to_string(), 2560),
            ("Quadro M5000".to_string(), 2048),

            ("GeForce RTX 2080 Ti".to_string(), 4352),
            ("GeForce RTX 2080 SUPER".to_string(), 3072),
            ("GeForce RTX 2080".to_string(), 2944),
            ("GeForce RTX 2070 SUPER".to_string(), 2560),

            ("GeForce GTX 1080 Ti".to_string(), 3584),
            ("GeForce GTX 1080".to_string(), 2560),
            ("GeForce GTX 2060".to_string(), 1920),
            ("GeForce GTX 1660 Ti".to_string(), 1536),
            ("GeForce GTX 1060".to_string(), 1280),
            ("GeForce GTX 1650 SUPER".to_string(), 1280),
            ("GeForce GTX 1650".to_string(), 896),
        ].into_iter().collect();

        match env::var("BELLMAN_CUSTOM_GPU").and_then(|var| {
            for card in var.split(",") {
                let splitted = card.split(":").collect::<Vec<_>>();
                if splitted.len() != 2 { panic!("Invalid BELLMAN_CUSTOM_GPU!"); }
                let name = splitted[0].trim().to_string();
                let cores : usize = splitted[1].trim().parse().expect("Invalid BELLMAN_CUSTOM_GPU!");
                info!("Adding \"{}\" to GPU list with {} CUDA cores.", name, cores);
                core_counts.insert(name, cores);
            }
            Ok(())
        }) { Err(_) => { }, Ok(_) => { } }

        core_counts
    };
}

const DEFAULT_CORE_COUNT: usize = 2560;
pub fn get_core_count(d: Device) -> GPUResult<usize> {
    let name = d.name()?;
    match CORE_COUNTS.get(&name[..]) {
        Some(&cores) => Ok(cores),
        None => {
            warn!(
                "Number of CUDA cores for your device ({}) is unknown! Best performance is \
                 only achieved when the number of CUDA cores is known! You can find the \
                 instructions on how to support custom GPUs here: \
                 https://lotu.sh/en+hardware-mining",
                name
            );
            Ok(DEFAULT_CORE_COUNT)
        }
    }
}

pub fn get_memory(d: Device) -> GPUResult<u64> {
    match d.info(ocl::enums::DeviceInfo::GlobalMemSize)? {
        ocl::enums::DeviceInfoResult::GlobalMemSize(sz) => Ok(sz),
        _ => Err(GPUError::Simple("Cannot extract GPU memory!")),
    }
}
