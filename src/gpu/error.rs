#[derive(thiserror::Error, Debug)]
pub enum GPUError {
    #[error("GPUError: {0}")]
    Simple(&'static str),
    #[cfg(feature = "gpu")]
    #[error("Ocl Error: {0}")]
    Ocl(ocl::Error),
}

pub type GPUResult<T> = std::result::Result<T, GPUError>;

#[cfg(feature = "gpu")]
impl From<ocl::Error> for GPUError {
    fn from(error: ocl::Error) -> Self {
        GPUError::Ocl(error)
    }
}

#[cfg(feature = "gpu")]
impl From<std::boxed::Box<dyn std::any::Any + std::marker::Send>> for GPUError {
    fn from(e: std::boxed::Box<dyn std::any::Any + std::marker::Send>) -> Self {
        match e.downcast::<Self>() {
            Ok(err) => *err,
            Err(_) => GPUError::Simple("An unknown GPU error happened!"),
        }
    }
}
