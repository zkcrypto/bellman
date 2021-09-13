//! An interface for dealing with the kinds of parallel computations involved in
//! `bellman`. It's currently just a thin wrapper around [`rayon`] but may be
//! extended in the future to allow for various parallelism strategies.

#[cfg(feature = "multicore")]
mod implementation {
    use std::sync::atomic::{AtomicUsize, Ordering};

    use crossbeam_channel::{bounded, Receiver};
    use lazy_static::lazy_static;
    use log::{error, trace};
    use rayon::current_num_threads;

    static WORKER_SPAWN_COUNTER: AtomicUsize = AtomicUsize::new(0);

    lazy_static! {
        // See Worker::compute below for a description of this.
        static ref WORKER_SPAWN_MAX_COUNT: usize = current_num_threads() * 4;
    }

    #[derive(Clone, Default)]
    pub struct Worker {}

    impl Worker {
        pub fn new() -> Worker {
            Worker {}
        }

        pub fn log_num_threads(&self) -> u32 {
            log2_floor(current_num_threads())
        }

        pub fn compute<F, R>(&self, f: F) -> Waiter<R>
        where
            F: FnOnce() -> R + Send + 'static,
            R: Send + 'static,
        {
            let (sender, receiver) = bounded(1);

            // We keep track here of how many times spawn has been called.
            // It can be called without limit, each time, putting a
            // request for a new thread to execute a method on the
            // ThreadPool.  However, if we allow it to be called without
            // limits, we run the risk of memory exhaustion due to limited
            // stack space consumed by all of the pending closures to be
            // executed.
            let previous_count = WORKER_SPAWN_COUNTER.fetch_add(1, Ordering::SeqCst);

            // If the number of spawns requested has exceeded the number
            // of cores available for processing by some factor (the
            // default being 4), instead of requesting that we spawn a new
            // thread, we instead execute the closure in the context of a
            // scope call (which blocks the current thread) to help clear
            // the growing work queue and minimize the chances of memory
            // exhaustion.
            if previous_count > *WORKER_SPAWN_MAX_COUNT {
                let thread_index = rayon::current_thread_index().unwrap_or(0);
                rayon::scope(move |_| {
                    trace!("[{}] switching to scope to help clear backlog [threads: current {}, requested {}]",
                        thread_index,
                        current_num_threads(),
                        WORKER_SPAWN_COUNTER.load(Ordering::SeqCst));
                    let res = f();
                    sender.send(res).unwrap();
                    WORKER_SPAWN_COUNTER.fetch_sub(1, Ordering::SeqCst);
                });
            } else {
                rayon::spawn(move || {
                    let res = f();
                    sender.send(res).unwrap();
                    WORKER_SPAWN_COUNTER.fetch_sub(1, Ordering::SeqCst);
                });
            }

            Waiter { receiver }
        }

        pub fn scope<'a, F, R>(&self, elements: usize, f: F) -> R
        where
            F: FnOnce(&rayon::Scope<'a>, usize) -> R + Send,
            R: Send,
        {
            let num_threads = current_num_threads();
            let chunk_size = if elements < num_threads {
                1
            } else {
                elements / num_threads
            };

            rayon::scope(|scope| f(scope, chunk_size))
        }
    }

    pub struct Waiter<T> {
        receiver: Receiver<T>,
    }

    impl<T> Waiter<T> {
        /// Consumes this waiter and blocks until the result is ready.
        pub fn wait(self) -> T {
            // This will be Some if this thread is in the global thread pool.
            if rayon::current_thread_index().is_some() {
                let msg = "wait() cannot be called from within a thread pool since that would lead to deadlocks";
                // panic! doesn't necessarily kill the process, so we log as well.
                error!("{}", msg);
                panic!("{}", msg);
            }
            self.receiver.recv().unwrap()
        }

        /// One-off sending.
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

        pub fn log_num_threads(&self) -> u32 {
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
        /// Consumes this waiter and blocks until the result is ready.
        pub fn wait(mut self) -> T {
            self.val.take().expect("unmet data dependency")
        }

        /// One-off sending.
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
