//! An interface for dealing with the kinds of parallel computations involved in
//! `bellman`. It's currently just a thin wrapper around [`CpuPool`] and
//! [`rayon`] but may be extended in the future to allow for various
//! parallelism strategies.
//!
//! [`CpuPool`]: futures_cpupool::CpuPool

#[cfg(feature = "multicore")]
mod implementation {
    use std::env;

    use crossbeam_channel::{bounded, Receiver};
    use lazy_static::lazy_static;
    use log::error;
    use num_cpus;

    lazy_static! {
        static ref NUM_CPUS: usize = if let Ok(num) = env::var("BELLMAN_NUM_CPUS") {
            if let Ok(num) = num.parse() {
                num
            } else {
                num_cpus::get()
            }
        } else {
            num_cpus::get()
        };
        pub static ref THREAD_POOL: rayon::ThreadPool = rayon::ThreadPoolBuilder::new()
            .num_threads(*NUM_CPUS)
            .build()
            .unwrap();
    }

    #[derive(Clone)]
    pub struct Worker {}

    impl Worker {
        pub fn new() -> Worker {
            Worker {}
        }

        pub fn log_num_cpus(&self) -> u32 {
            log2_floor(*NUM_CPUS)
        }

        pub fn compute<F, R>(&self, f: F) -> Waiter<R>
        where
            F: FnOnce() -> R + Send + 'static,
            R: Send + 'static,
        {
            let (sender, receiver) = bounded(1);
            THREAD_POOL.spawn(move || {
                let res = f();
                sender.send(res).unwrap();
            });

            Waiter { receiver }
        }

        pub fn scope<'a, F, R>(&self, elements: usize, f: F) -> R
        where
            F: FnOnce(&rayon::Scope<'a>, usize) -> R + Send,
            R: Send,
        {
            let chunk_size = if elements < *NUM_CPUS {
                1
            } else {
                elements / *NUM_CPUS
            };

            THREAD_POOL.scope(|scope| f(scope, chunk_size))
        }
    }

    pub struct Waiter<T> {
        receiver: Receiver<T>,
    }

    impl<T> Waiter<T> {
        /// Wait for the result.
        pub fn wait(&self) -> T {
            if THREAD_POOL.current_thread_index().is_some() {
                // Calling `wait()` from within the worker thread pool can lead to dead logs
                error!("The wait call should never be done inside the worker thread pool");
                debug_assert!(false);
            }
            self.receiver.recv().unwrap()
        }

        /// One off sending.
        pub fn done(val: T) -> Self {
            let (sender, receiver) = bounded(1);
            sender.send(val).unwrap();

            Waiter { receiver }
        }
    }

    fn log2_floor(num: usize) -> u32 {
        assert!(num > 0);

        let mut pow = 0;

        while (1 << (pow + 1)) <= num {
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
}

#[cfg(not(feature = "multicore"))]
mod implementation {
    #[derive(Clone)]
    pub struct Worker;

    impl Worker {
        pub fn new() -> Worker {
            Worker
        }

        pub fn log_num_cpus(&self) -> u32 {
            0
        }

        pub fn compute<F, R>(&self, f: F) -> Waiter<R>
        where
            F: FnOnce() -> R + Send + 'static,
            R: Send + 'static,
        {
            Waiter::done(f())
        }

        pub fn scope<F, R>(&self, elements: usize, f: F) -> R
        where
            F: FnOnce(&DummyScope, usize) -> R,
        {
            f(&DummyScope, elements)
        }
    }

    pub struct Waiter<T> {
        val: Option<T>,
    }

    impl<T> Waiter<T> {
        /// Wait for the result.
        pub fn wait(&mut self) -> T {
            self.val.take().unwrap()
        }

        /// One off sending.
        pub fn done(val: T) -> Self {
            Waiter { val: Some(val) }
        }
    }

    pub struct DummyScope;

    impl DummyScope {
        pub fn spawn<F: FnOnce(&DummyScope)>(&self, f: F) {
            f(self);
        }
    }

    /// A fake rayon ParallelIterator that is just a serial iterator.
    pub(crate) trait FakeParallelIterator {
        type Iter: Iterator<Item = Self::Item>;
        type Item: Send;
        fn into_par_iter(self) -> Self::Iter;
    }

    impl FakeParallelIterator for core::ops::Range<u32> {
        type Iter = Self;
        type Item = u32;
        fn into_par_iter(self) -> Self::Iter {
            self
        }
    }
}

pub use self::implementation::*;
