//! This is an interface for dealing with the kinds of
//! parallel computations involved in bellman. It's
//! currently just a thin wrapper around CpuPool and
//! crossbeam but may be extended in the future to
//! allow for various parallelism strategies.

extern crate num_cpus;
extern crate futures;
extern crate futures_cpupool;
extern crate crossbeam;

use self::futures::{Future, IntoFuture, Poll};
use self::futures_cpupool::{CpuPool, CpuFuture};
use self::crossbeam::thread::{Scope};

#[derive(Clone)]
pub struct Worker {
    pub(crate) cpus: usize,
    pool: CpuPool
}

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
        let cpus = num_cpus::get();
        Self::new_with_cpus(cpus)
    }

    pub fn log_num_cpus(&self) -> u32 {
        log2_floor(self.cpus)
    }

    pub fn num_cpus(&self) -> u32 {
        self.cpus as u32
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
        let chunk_size = self.get_chunk_size(elements);

        crossbeam::scope(|scope| {
            f(scope, chunk_size)
        }).expect("must run")
    }

    pub fn get_chunk_size(
        &self,
        elements: usize
    ) -> usize {
        let chunk_size = if elements < self.cpus {
            1
        } else {
            elements / self.cpus
        };

        chunk_size
    }

    pub fn get_num_spawned_threads(
        &self,
        elements: usize
    ) -> usize {
        let chunk_size = self.get_chunk_size(elements);

        let mut n = elements / chunk_size;
        if elements % chunk_size != 0 {
            n += 1;
        }

        n
    }
}

pub struct WorkerFuture<T, E> {
    future: CpuFuture<T, E>
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
    assert_eq!(log2_floor(15), 3);
    assert_eq!(log2_floor(16), 4);
}
