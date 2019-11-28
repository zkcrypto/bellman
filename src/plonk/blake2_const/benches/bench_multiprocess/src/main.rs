//! There are many sources of variability in the performance of these BLAKE2
//! functions:
//!
//! 1. Random noise. We do many runs to average the noise out.
//! 2. Random noise that's sticky to a given process. See:
//!    https://blog.phusion.nl/2017/07/13/understanding-your-benchmarks-and-easy-tips-for-fixing-them
//!    We split the runs over many worker processes to average this out.
//! 3. Variable memory throughput depending on the offset of the input. See:
//!    https://github.com/oconnor663/blake2b_simd/issues/8
//!
//! That offset effect especially troublesome. The overall throughput of
//! BLAKE2bp at the "worst" offset is several percentage points lower than at
//! the "best". Furthermore, the relationship between offset and throughput is
//! quite complicated -- there's no simple rule like "start at a page boundary"
//! that papers over the problem. (A blunt approach like that tend to pessimize
//! BLAKE2bp in favor of many::hash, which suffers less from this effect when
//! its multiple inputs are at uncorrelated offsets.) The size of the effect
//! also grows with the length of the input; 100 MB inputs show it more than 1
//! MB inputs, probably due to caching effects.
//!
//! Currently we try to address this by averaging over throughput at every
//! possible input offset. Experiments at
//! https://github.com/oconnor663/blake2b_simd/issues/8 show that the offset
//! effect has a period of 512 bytes, so we run every offset from 0 to 511.
//! This does seem to produce stable results, though it raises tricky questions
//! about how real world performance will compare to these benchmarks. For
//! example, real world inputs will probably sit at whatever offset the global
//! memory allocator produces, which 1) isn't random at all and 2) probably
//! varies depending on memory pressure. But such is life for benchmarks.

extern crate blake2b_simd;

use rand::seq::SliceRandom;
use rand::RngCore;
use std::cmp::Ordering::{Greater, Less};
use std::env;
use std::io::prelude::*;
use std::process;
use std::ptr;
use std::str;
use std::time::Instant;

const WORKERS: usize = 100;

// 512 is the measured period of the offset effect in BLAKE2bp.
// See https://github.com/oconnor663/blake2b_simd/issues/8.
const OFFSET_PERIOD: usize = 512;

const BENCH_LEN: usize = 1_000_000;

static ALGOS: &[(&str, HashBench)] = &[
    ("blake2b_simd BLAKE2b", blake2b_hash),
    ("blake2b_simd many", blake2b_hash_many),
    ("blake2b_simd BLAKE2bp", hash_blake2bp),
    ("blake2s_simd BLAKE2s", blake2s_hash),
    ("blake2s_simd many", blake2s_hash_many),
    ("blake2s_simd BLAKE2sp", hash_blake2sp),
    ("sneves BLAKE2b", hash_sneves_blake2b),
    ("sneves BLAKE2bp", hash_sneves_blake2bp),
    ("sneves BLAKE2sp", hash_sneves_blake2sp),
    ("libsodium BLAKE2b", libsodium),
    ("OpenSSL SHA-1", openssl_sha1),
    ("OpenSSL SHA-512", openssl_sha512),
];

type HashBench = fn() -> u128;

fn bench(mut f: impl FnMut()) -> u128 {
    // dummy run
    f();
    // real timed runs
    let before = Instant::now();
    for _ in 0..OFFSET_PERIOD {
        f();
    }
    let after = Instant::now();
    (after - before).as_nanos()
}

fn blake2b_hash() -> u128 {
    let mut input = OffsetInput::new(BENCH_LEN);
    bench(|| {
        blake2b_simd::blake2b(input.get());
    })
}

fn blake2s_hash() -> u128 {
    let mut input = OffsetInput::new(BENCH_LEN);
    bench(|| {
        blake2s_simd::blake2s(input.get());
    })
}

// This one does each run with N=degree inputs at the same offset. This leads
// to an offset effect comparable to what we see with BLAKE2bp.
// fn blake2b_hash_many_correlated() -> u128 {
//     let degree = blake2b_simd::many::degree();
//     let bench_len = BENCH_LEN / degree;
//     let mut inputs = Vec::new();
//     for _ in 0..degree {
//         inputs.push(OffsetInput::new(bench_len));
//     }
//     let params = blake2b_simd::Params::new();
//     bench(|| {
//         let mut jobs = arrayvec::ArrayVec::<[_; blake2b_simd::many::MAX_DEGREE]>::new();
//         for input in &mut inputs {
//             let job = blake2b_simd::many::HashManyJob::new(&params, input.get());
//             jobs.push(job);
//         }
//         blake2b_simd::many::hash_many(&mut jobs);
//     })
// }

// This one does each run with N=degree inputs at uncorrelated offsets. This
// turns out to reduce the offset effect and give better performance. This is
// currently the number I report in the crate documentation. On the one hand,
// that's a self-serving decision, because it's a higher number. On the other
// hand, the fact that numbers are different is pretty important, and I don't
// want to bury it.
fn blake2b_hash_many() -> u128 {
    let degree = blake2b_simd::many::degree();
    let bench_len = BENCH_LEN / degree;
    let mut inputs = Vec::new();
    for _ in 0..degree {
        let mut offset_input = OffsetInput::new(bench_len);
        offset_input.offsets.shuffle();
        inputs.push(OffsetInput::new(bench_len));
    }
    let params = blake2b_simd::Params::new();
    bench(|| {
        let mut jobs = arrayvec::ArrayVec::<[_; blake2b_simd::many::MAX_DEGREE]>::new();
        for input in &mut inputs {
            let job = blake2b_simd::many::HashManyJob::new(&params, input.get());
            jobs.push(job);
        }
        blake2b_simd::many::hash_many(&mut jobs);
    })
}

fn blake2s_hash_many() -> u128 {
    let degree = blake2s_simd::many::degree();
    let bench_len = BENCH_LEN / degree;
    let mut inputs = Vec::new();
    for _ in 0..degree {
        let mut offset_input = OffsetInput::new(bench_len);
        offset_input.offsets.shuffle();
        inputs.push(OffsetInput::new(bench_len));
    }
    let params = blake2s_simd::Params::new();
    bench(|| {
        let mut jobs = arrayvec::ArrayVec::<[_; blake2s_simd::many::MAX_DEGREE]>::new();
        for input in &mut inputs {
            let job = blake2s_simd::many::HashManyJob::new(&params, input.get());
            jobs.push(job);
        }
        blake2s_simd::many::hash_many(&mut jobs);
    })
}

fn hash_blake2bp() -> u128 {
    let mut input = OffsetInput::new(BENCH_LEN);
    bench(|| {
        blake2b_simd::blake2bp::blake2bp(input.get());
    })
}

fn hash_blake2sp() -> u128 {
    let mut input = OffsetInput::new(BENCH_LEN);
    bench(|| {
        blake2s_simd::blake2sp::blake2sp(input.get());
    })
}

fn hash_sneves_blake2b() -> u128 {
    let mut input = OffsetInput::new(BENCH_LEN);
    bench(|| {
        blake2_avx2_sneves::blake2b(input.get());
    })
}

fn hash_sneves_blake2bp() -> u128 {
    let mut input = OffsetInput::new(BENCH_LEN);
    bench(|| {
        blake2_avx2_sneves::blake2bp(input.get());
    })
}

fn hash_sneves_blake2sp() -> u128 {
    let mut input = OffsetInput::new(BENCH_LEN);
    bench(|| {
        blake2_avx2_sneves::blake2sp(input.get());
    })
}

fn libsodium() -> u128 {
    let mut input = OffsetInput::new(BENCH_LEN);
    bench(|| {
        let mut out = [0; 64];
        unsafe {
            let init_ret = libsodium_ffi::sodium_init();
            assert!(init_ret != -1);
        }
        let input_slice = input.get();
        unsafe {
            libsodium_ffi::crypto_generichash(
                out.as_mut_ptr(),
                out.len(),
                input_slice.as_ptr(),
                input_slice.len() as u64,
                ptr::null(),
                0,
            );
        };
    })
}

fn openssl_sha1() -> u128 {
    let mut input = OffsetInput::new(BENCH_LEN);
    bench(|| {
        openssl::hash::hash(openssl::hash::MessageDigest::sha1(), input.get()).unwrap();
    })
}

fn openssl_sha512() -> u128 {
    let mut input = OffsetInput::new(BENCH_LEN);
    bench(|| {
        openssl::hash::hash(openssl::hash::MessageDigest::sha512(), input.get()).unwrap();
    })
}

struct VecIter<T> {
    vec: Vec<T>,
    i: usize,
}

impl<T: Clone> VecIter<T> {
    fn next(&mut self) -> T {
        let item = self.vec[self.i].clone();
        self.i += 1;
        if self.i >= self.vec.len() {
            self.i = 0;
        }
        item
    }

    fn shuffle(&mut self) {
        self.vec.shuffle(&mut rand::thread_rng());
    }
}

// This struct serves inputs that rotate through all possible memory offsets
// relative to OFFSET_PERIOD.
struct OffsetInput {
    buf: Vec<u8>,
    len: usize,
    offsets: VecIter<usize>,
}

impl OffsetInput {
    fn new(len: usize) -> Self {
        let mut buf = vec![0u8; len + OFFSET_PERIOD];
        rand::thread_rng().fill_bytes(&mut buf);
        // Make each offset absolute in the address space, by adjusting for
        // where the Vec was allocated.
        let adjustment = OFFSET_PERIOD - (buf.as_ptr() as usize % OFFSET_PERIOD);
        let offsets: Vec<usize> = (0..OFFSET_PERIOD)
            .map(|off| (off + adjustment) % OFFSET_PERIOD)
            .collect();
        Self {
            buf,
            len,
            offsets: VecIter { vec: offsets, i: 0 },
        }
    }

    fn get(&mut self) -> &[u8] {
        &self.buf[self.offsets.next()..][..self.len]
    }
}

fn get_hash_bench(name: &str) -> HashBench {
    let mut hash_fn = None;
    for &(algo_name, f) in ALGOS {
        if name == algo_name {
            hash_fn = Some(f);
            break;
        }
    }
    hash_fn.expect(&format!("no such algo: {}", name))
}

// Note that bytes/nanosecond and GB/second are the same unit.
fn rate_f32(ns: u128, input_len: usize) -> f32 {
    input_len as f32 / ns as f32
}

fn worker(algo: &str) {
    let hash_bench = get_hash_bench(algo);
    let total_ns = hash_bench();
    println!("{}", total_ns);
}

fn run_algo(algo_name: &str) -> f32 {
    // Fire off all the workers in series and collect their reported times.
    let mut _times = Vec::new();
    let mut _total_ns = 0;
    for _ in 0..WORKERS {
        env::set_var("BENCH_ALGO", algo_name);
        let mut cmd = process::Command::new(env::current_exe().unwrap());
        cmd.stdout(process::Stdio::piped());
        let child = cmd.spawn().unwrap();
        let output = child.wait_with_output().unwrap();
        let ns: u128 = str::from_utf8(&output.stdout)
            .unwrap()
            .trim()
            .parse()
            .unwrap();
        // eprintln!(
        //     "worker throughput: {}",
        //     rate_f32(ns, RUNS_PER_WORKER * worker_len)
        // );
        _times.push(ns);
        _total_ns += ns;
    }
    _times.sort();
    let throughput = rate_f32(_total_ns, WORKERS * OFFSET_PERIOD * BENCH_LEN);

    // eprintln!("final throughput: {}", throughput);
    throughput
}

fn main() {
    if let Ok(name) = env::var("BENCH_ALGO") {
        worker(&name);
        return;
    }

    // If a positional argument is given, it should be a substring of exactly
    // one algorithm name. In that case, run just that algorithm, and print the
    // result with no other formatting.
    if let Some(arg) = std::env::args().nth(1) {
        let matches: Vec<&str> = ALGOS
            .iter()
            .map(|&(name, _)| name)
            .filter(|&name| name == arg.as_str())
            .collect();
        if matches.is_empty() {
            panic!("no match");
        }
        if matches.len() > 1 {
            panic!("too many matches {:?}", &matches);
        }
        let algo_name = matches[0];
        let throughput = run_algo(algo_name);
        println!("{:.3}", throughput);
        return;
    }

    // Otherwise run all the benchmarks and print them sorted at the end.
    let mut throughputs = Vec::new();
    for &(algo_name, _) in ALGOS {
        print!("{}: ", algo_name);
        std::io::stdout().flush().unwrap();

        let throughput = run_algo(algo_name);
        throughputs.push((throughput, algo_name));

        println!("{:.3}", throughput);
    }

    // Sort by the fastest rate.
    throughputs.sort_by(|t1, t2| if t1.0 > t2.0 { Less } else { Greater });

    let max_name_len = ALGOS.iter().map(|(name, _)| name.len()).max().unwrap();
    println!("\nIn order:");
    for &(throughput, name) in &throughputs {
        println!("{0:1$} {2:.3}", name, max_name_len, throughput);
    }
}
