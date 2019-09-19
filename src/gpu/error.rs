use std::error;
use std::fmt;

#[derive(Debug, Clone)]
pub struct GPUError {
    pub msg: String
}

pub type GPUResult<T> = std::result::Result<T, GPUError>;

impl fmt::Display for GPUError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.msg)
    }
}

impl error::Error for GPUError {
    fn description(&self) -> &str {
        self.msg.as_str()
    }

    fn cause(&self) -> Option<&error::Error> {
        None
    }
}

#[cfg(feature = "gpu")]
use ocl;

#[cfg(feature = "gpu")]
impl From<ocl::Error> for GPUError {
    fn from(error: ocl::Error) -> Self {
        GPUError {msg: error.to_string() }
    }
}
