//! This is an interface for dealing with the kinds of
//! parallel computations involved in bellman. It's
//! currently just an optional thin wrapper around CpuPool and
//! crossbeam but may be extended in the future to
//! allow for various parallelism strategies.
//! Compile without the "multithread" feature for targets that
//! don't support parallel computation.

use futures::{Future, IntoFuture, Poll};

#[cfg(feature = "multithread")]
use num_cpus;
#[cfg(feature = "multithread")]
use futures_cpupool::{CpuPool, CpuFuture};
#[cfg(feature = "multithread")]
use crossbeam::{self, Scope};

#[cfg(not(feature = "multithread"))]
use futures::future::{result, FutureResult};

#[cfg(feature = "multithread")]
#[derive(Clone)]
pub struct Worker {
    cpus: usize,
    pool: CpuPool
}

#[cfg(feature = "multithread")]
impl Worker {
    // We don't expose this outside the library so that
    // all `Worker` instances have the same number of
    // CPUs configured.
    pub(crate) fn new_with_cpus(cpus: usize) -> Worker {

        Worker {
            cpus: cpus,
            pool: CpuPool::new(cpus)
        }
    }

    pub fn new() -> Worker {
        Self::new_with_cpus(num_cpus::get())
    }

    pub fn log_num_cpus(&self) -> u32 {
        log2_floor(self.cpus)
    }

    pub fn compute<F, R>(
        &self, f: F
    ) -> WorkerFuture<R::Item, R::Error>
        where F: FnOnce() -> R + Send + 'static,
              R: IntoFuture + 'static,
              R::Future: Send + 'static,
              R::Item: Send + 'static,
              R::Error: Send + 'static
    {
        WorkerFuture {
            future: self.pool.spawn_fn(f)
        }
    }

    pub fn scope<'a, F, R>(
        &self,
        elements: usize,
        f: F
    ) -> R
        where F: FnOnce(&Scope<'a>, usize) -> R
    {
        let chunk_size = if elements < self.cpus {
            1
        } else {
            elements / self.cpus
        };

        crossbeam::scope(|scope| {
            f(scope, chunk_size)
        })
    }
}

#[cfg(feature = "multithread")]
pub struct WorkerFuture<T, E> {
    future: CpuFuture<T, E>
}

//Dummy worker for single-threaded mode
#[cfg(not(feature = "multithread"))]
#[derive(Clone)]
pub struct Worker {}

#[cfg(not(feature = "multithread"))]
impl Worker {

    pub fn new() -> Worker { Worker {} } 

    pub fn log_num_cpus(&self) -> u32 {
        log2_floor(1)
    }

    pub fn compute<F, R>(
        &self, f: F
    ) -> WorkerFuture<R::Item, R::Error>
        where F: FnOnce() -> R,
              R: IntoFuture + 'static,
              R::Future: Send + 'static,
              R::Item: Send + 'static,
              R::Error: Send + 'static
    {
        let future = f().into_future();

        WorkerFuture {
            future: result(future.wait())
        }
    }

    pub fn scope<F, R>(
        &self,
        _elements: usize,
        f: F
    ) -> R
        where F: FnOnce(&Scope, usize) -> R
    {
        let scope = Scope {};  
        f(&scope, 1)
    }
}

//
#[cfg(not(feature = "multithread"))]
pub struct Scope {
}

#[cfg(not(feature = "multithread"))]
impl Scope {
pub fn spawn<F, T>(&self, f: F) -> T  where
        F: FnOnce() -> T + Send , T: Send 
    {
        f()
    }

}

#[cfg(not(feature = "multithread"))]
pub struct WorkerFuture<T, E> {
    future: FutureResult<T, E>
}

impl<T: Send + 'static, E: Send + 'static> Future for WorkerFuture<T, E> {
    type Item = T;
    type Error = E;

    fn poll(&mut self) -> Poll<Self::Item, Self::Error>
    {
        self.future.poll()
    }
}

fn log2_floor(num: usize) -> u32 {
    assert!(num > 0);

    let mut pow = 0;

    while (1 << (pow+1)) <= num {
        pow += 1;
    }

    pow
}

#[test]
fn test_log2_floor() {
    assert_eq!(log2_floor(1), 0);
    assert_eq!(log2_floor(2), 1);
    assert_eq!(log2_floor(3), 1);
    assert_eq!(log2_floor(4), 2);
    assert_eq!(log2_floor(5), 2);
    assert_eq!(log2_floor(6), 2);
    assert_eq!(log2_floor(7), 2);
    assert_eq!(log2_floor(8), 3);
}