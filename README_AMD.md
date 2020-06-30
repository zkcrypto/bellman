# Using AMD GPUs

## Prerequisites

- [Install ROCm 3.5](https://rocmdocs.amd.com/en/latest/Installation_Guide/Installation-Guide.html#supported-operating-systems)

## Running tests

The environment variable `BELLMAN_PLATFORM` determines which backend will be used. 

To use the AMD backend, you can do something like: 

```bash
export BELLMAN_PLATFORM="AMD Accelerated Parallel Processing"
RUST_LOG=info cargo test --features gpu -- --exact multiexp::gpu_multiexp_consistency --nocapture
```

## Notes

- We had trouble in Ubuntu 20.04 when running a single computer with both NVIDIA and AMD cards. 
- The initial kernel compilation may take > 60sec at start up. This is not a problem afterwards. A possible mitigation would be to add kernel binary caching in the ocl-fil crate.
