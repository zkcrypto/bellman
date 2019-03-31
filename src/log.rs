#[allow(unused_macros)]

cfg_if! {
    if #[cfg(feature = "wasm")] {
        use web_sys;
        use web_sys::Performance;

        macro_rules! log {
            ($($t:tt)*) => (web_sys::console::log_1(&format_args!($($t)*).to_string().into()))
        }

        macro_rules! elog {
            ($($t:tt)*) => (web_sys::console::log_1(&format_args!($($t)*).to_string().into()))
        }

        macro_rules! log_verbose {
            ($($t:tt)*) => (if $crate::verbose_flag() { web_sys::console::log_1(&format_args!($($t)*).to_string().into()) })
        }

        macro_rules! elog_verbose {
            ($($t:tt)*) => (if $crate::verbose_flag() { web_sys::console::log_1(&format_args!($($t)*).to_string().into()) })
        }

        pub struct Stopwatch {
            start: f64,
            perf: Performance
        }

        impl Stopwatch {
            pub fn new() -> Stopwatch {
                let perf = web_sys::window().unwrap().performance().unwrap();
                Stopwatch { start: perf.now(), perf }
            }

            pub fn elapsed(&self) -> f64 {
                (self.perf.now() - self.start) / 1000.0
            }
        }
    } else {
        macro_rules! log {
            ($($t:tt)*) => (println!($($t)*))
        }

        macro_rules! elog {
            ($($t:tt)*) => (eprintln!($($t)*))
        }

        macro_rules! log_verbose {
            ($($t:tt)*) => (if $crate::verbose_flag() { println!($($t)*) })
        }

        macro_rules! elog_verbose {
            ($($t:tt)*) => (if $crate::verbose_flag() { eprintln!($($t)*) })
        }

        pub struct Stopwatch {
            start: std::time::Instant
        }

        impl Stopwatch {
            pub fn new() -> Stopwatch {
                Stopwatch { start: std::time::Instant::now() }
            }

            pub fn elapsed(&self) -> f64 {
                self.start.elapsed().as_millis() as f64 / 1000.0
            }
        }
    }
}