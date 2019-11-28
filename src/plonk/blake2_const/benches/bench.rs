#![feature(test)]

extern crate test;

use rand::seq::SliceRandom;
use rand::RngCore;
use test::Bencher;

const LONG: usize = 1 << 16; // 64 KiB

#[cfg(feature = "kangarootwelve")]
const VERYLONG: usize = 1 << 20; // 1 MiB

// This struct randomizes two things:
// 1. The actual bytes of input.
// 2. The page offset the input starts at.
struct RandomInput {
    buf: Vec<u8>,
    len: usize,
    offsets: Vec<usize>,
    offset_index: usize,
}

impl RandomInput {
    fn new(b: &mut Bencher, len: usize) -> Self {
        b.bytes += len as u64;
        let page_size: usize = page_size::get();
        let mut buf = vec![0u8; len + page_size];
        let mut rng = rand::thread_rng();
        rng.fill_bytes(&mut buf);
        let mut offsets: Vec<usize> = (0..page_size).collect();
        offsets.shuffle(&mut rng);
        Self {
            buf,
            len,
            offsets,
            offset_index: 0,
        }
    }

    fn get(&mut self) -> &[u8] {
        let offset = self.offsets[self.offset_index];
        self.offset_index += 1;
        if self.offset_index >= self.offsets.len() {
            self.offset_index = 0;
        }
        &self.buf[offset..][..self.len]
    }
}

#[bench]
fn bench_oneblock_blake2b_avx2(b: &mut Bencher) {
    let mut input = RandomInput::new(b, blake2b_simd::BLOCKBYTES);
    b.iter(|| blake2b_simd::blake2b(input.get()));
}

#[bench]
fn bench_onebyte_blake2b_avx2(b: &mut Bencher) {
    b.iter(|| blake2b_simd::blake2b(b"x"));
}

#[bench]
fn bench_long_blake2b_avx2(b: &mut Bencher) {
    let mut input = RandomInput::new(b, LONG);
    b.iter(|| blake2b_simd::blake2b(input.get()));
}

#[bench]
fn bench_oneblock_blake2b_portable(b: &mut Bencher) {
    let mut input = RandomInput::new(b, blake2b_simd::BLOCKBYTES);
    let mut params = blake2b_simd::Params::new();
    blake2b_simd::benchmarks::force_portable(&mut params);
    b.iter(|| params.hash(input.get()));
}

#[bench]
fn bench_long_blake2b_portable(b: &mut Bencher) {
    let mut input = RandomInput::new(b, LONG);
    let mut params = blake2b_simd::Params::new();
    blake2b_simd::benchmarks::force_portable(&mut params);
    b.iter(|| params.hash(input.get()));
}

#[bench]
fn bench_oneblock_blake2s_sse41(b: &mut Bencher) {
    let mut input = RandomInput::new(b, blake2s_simd::BLOCKBYTES);
    b.iter(|| blake2s_simd::blake2s(input.get()));
}

#[bench]
fn bench_onebyte_blake2s_sse41(b: &mut Bencher) {
    b.iter(|| blake2s_simd::blake2s(b"x"));
}

#[bench]
fn bench_long_blake2s_sse41(b: &mut Bencher) {
    let mut input = RandomInput::new(b, LONG);
    b.iter(|| blake2s_simd::blake2s(input.get()));
}

#[bench]
fn bench_oneblock_blake2s_portable(b: &mut Bencher) {
    let mut input = RandomInput::new(b, blake2s_simd::BLOCKBYTES);
    let mut params = blake2s_simd::Params::new();
    blake2s_simd::benchmarks::force_portable(&mut params);
    b.iter(|| params.hash(input.get()));
}

#[bench]
fn bench_long_blake2s_portable(b: &mut Bencher) {
    let mut input = RandomInput::new(b, LONG);
    let mut params = blake2s_simd::Params::new();
    blake2s_simd::benchmarks::force_portable(&mut params);
    b.iter(|| params.hash(input.get()));
}

#[bench]
fn bench_long_blake2bp(b: &mut Bencher) {
    let mut input = RandomInput::new(b, LONG);
    b.iter(|| blake2b_simd::blake2bp::blake2bp(input.get()));
}

#[bench]
fn bench_long_blake2sp(b: &mut Bencher) {
    let mut input = RandomInput::new(b, LONG);
    b.iter(|| blake2s_simd::blake2sp::blake2sp(input.get()));
}

#[bench]
fn bench_long_blake2b_many_2x(b: &mut Bencher) {
    let mut input0 = RandomInput::new(b, LONG);
    let mut input1 = RandomInput::new(b, LONG);
    let params = blake2b_simd::Params::new();
    b.iter(|| {
        let mut jobs = [
            blake2b_simd::many::HashManyJob::new(&params, input0.get()),
            blake2b_simd::many::HashManyJob::new(&params, input1.get()),
        ];
        blake2b_simd::many::hash_many(jobs.iter_mut());
        [jobs[0].to_hash(), jobs[1].to_hash()]
    });
}

#[bench]
fn bench_long_blake2b_many_4x(b: &mut Bencher) {
    let mut input0 = RandomInput::new(b, LONG);
    let mut input1 = RandomInput::new(b, LONG);
    let mut input2 = RandomInput::new(b, LONG);
    let mut input3 = RandomInput::new(b, LONG);
    let params = blake2b_simd::Params::new();
    b.iter(|| {
        let mut jobs = [
            blake2b_simd::many::HashManyJob::new(&params, input0.get()),
            blake2b_simd::many::HashManyJob::new(&params, input1.get()),
            blake2b_simd::many::HashManyJob::new(&params, input2.get()),
            blake2b_simd::many::HashManyJob::new(&params, input3.get()),
        ];
        blake2b_simd::many::hash_many(jobs.iter_mut());
        [
            jobs[0].to_hash(),
            jobs[1].to_hash(),
            jobs[2].to_hash(),
            jobs[3].to_hash(),
        ]
    });
}

#[bench]
fn bench_long_blake2s_many_4x(b: &mut Bencher) {
    let mut input0 = RandomInput::new(b, LONG);
    let mut input1 = RandomInput::new(b, LONG);
    let mut input2 = RandomInput::new(b, LONG);
    let mut input3 = RandomInput::new(b, LONG);
    let params = blake2s_simd::Params::new();
    b.iter(|| {
        let mut jobs = [
            blake2s_simd::many::HashManyJob::new(&params, input0.get()),
            blake2s_simd::many::HashManyJob::new(&params, input1.get()),
            blake2s_simd::many::HashManyJob::new(&params, input2.get()),
            blake2s_simd::many::HashManyJob::new(&params, input3.get()),
        ];
        blake2s_simd::many::hash_many(jobs.iter_mut());
        [
            jobs[0].to_hash(),
            jobs[1].to_hash(),
            jobs[2].to_hash(),
            jobs[3].to_hash(),
        ]
    });
}

#[bench]
fn bench_long_blake2s_many_8x(b: &mut Bencher) {
    let mut input0 = RandomInput::new(b, LONG);
    let mut input1 = RandomInput::new(b, LONG);
    let mut input2 = RandomInput::new(b, LONG);
    let mut input3 = RandomInput::new(b, LONG);
    let mut input4 = RandomInput::new(b, LONG);
    let mut input5 = RandomInput::new(b, LONG);
    let mut input6 = RandomInput::new(b, LONG);
    let mut input7 = RandomInput::new(b, LONG);
    let params = blake2s_simd::Params::new();
    b.iter(|| {
        let mut jobs = [
            blake2s_simd::many::HashManyJob::new(&params, input0.get()),
            blake2s_simd::many::HashManyJob::new(&params, input1.get()),
            blake2s_simd::many::HashManyJob::new(&params, input2.get()),
            blake2s_simd::many::HashManyJob::new(&params, input3.get()),
            blake2s_simd::many::HashManyJob::new(&params, input4.get()),
            blake2s_simd::many::HashManyJob::new(&params, input5.get()),
            blake2s_simd::many::HashManyJob::new(&params, input6.get()),
            blake2s_simd::many::HashManyJob::new(&params, input7.get()),
        ];
        blake2s_simd::many::hash_many(jobs.iter_mut());
        [
            jobs[0].to_hash(),
            jobs[1].to_hash(),
            jobs[2].to_hash(),
            jobs[3].to_hash(),
            jobs[4].to_hash(),
            jobs[5].to_hash(),
            jobs[6].to_hash(),
            jobs[7].to_hash(),
        ]
    });
}

#[bench]
fn bench_oneblock_blake2b_many_2x(b: &mut Bencher) {
    let mut input0 = RandomInput::new(b, blake2b_simd::BLOCKBYTES);
    let mut input1 = RandomInput::new(b, blake2b_simd::BLOCKBYTES);
    let params = blake2b_simd::Params::new();
    b.iter(|| {
        let mut jobs = [
            blake2b_simd::many::HashManyJob::new(&params, input0.get()),
            blake2b_simd::many::HashManyJob::new(&params, input1.get()),
        ];
        blake2b_simd::many::hash_many(jobs.iter_mut());
        [jobs[0].to_hash(), jobs[1].to_hash()]
    });
}

#[bench]
fn bench_oneblock_blake2b_many_4x(b: &mut Bencher) {
    let mut input0 = RandomInput::new(b, blake2b_simd::BLOCKBYTES);
    let mut input1 = RandomInput::new(b, blake2b_simd::BLOCKBYTES);
    let mut input2 = RandomInput::new(b, blake2b_simd::BLOCKBYTES);
    let mut input3 = RandomInput::new(b, blake2b_simd::BLOCKBYTES);
    let params = blake2b_simd::Params::new();
    b.iter(|| {
        let mut jobs = [
            blake2b_simd::many::HashManyJob::new(&params, input0.get()),
            blake2b_simd::many::HashManyJob::new(&params, input1.get()),
            blake2b_simd::many::HashManyJob::new(&params, input2.get()),
            blake2b_simd::many::HashManyJob::new(&params, input3.get()),
        ];
        blake2b_simd::many::hash_many(jobs.iter_mut());
        [
            jobs[0].to_hash(),
            jobs[1].to_hash(),
            jobs[2].to_hash(),
            jobs[3].to_hash(),
        ]
    });
}

#[bench]
fn bench_oneblock_blake2s_many_4x(b: &mut Bencher) {
    let mut input0 = RandomInput::new(b, blake2s_simd::BLOCKBYTES);
    let mut input1 = RandomInput::new(b, blake2s_simd::BLOCKBYTES);
    let mut input2 = RandomInput::new(b, blake2s_simd::BLOCKBYTES);
    let mut input3 = RandomInput::new(b, blake2s_simd::BLOCKBYTES);
    let params = blake2s_simd::Params::new();
    b.iter(|| {
        let mut jobs = [
            blake2s_simd::many::HashManyJob::new(&params, input0.get()),
            blake2s_simd::many::HashManyJob::new(&params, input1.get()),
            blake2s_simd::many::HashManyJob::new(&params, input2.get()),
            blake2s_simd::many::HashManyJob::new(&params, input3.get()),
        ];
        blake2s_simd::many::hash_many(jobs.iter_mut());
        [
            jobs[0].to_hash(),
            jobs[1].to_hash(),
            jobs[2].to_hash(),
            jobs[3].to_hash(),
        ]
    });
}

#[bench]
fn bench_oneblock_blake2s_many_8x(b: &mut Bencher) {
    let mut input0 = RandomInput::new(b, blake2s_simd::BLOCKBYTES);
    let mut input1 = RandomInput::new(b, blake2s_simd::BLOCKBYTES);
    let mut input2 = RandomInput::new(b, blake2s_simd::BLOCKBYTES);
    let mut input3 = RandomInput::new(b, blake2s_simd::BLOCKBYTES);
    let mut input4 = RandomInput::new(b, blake2s_simd::BLOCKBYTES);
    let mut input5 = RandomInput::new(b, blake2s_simd::BLOCKBYTES);
    let mut input6 = RandomInput::new(b, blake2s_simd::BLOCKBYTES);
    let mut input7 = RandomInput::new(b, blake2s_simd::BLOCKBYTES);
    let params = blake2s_simd::Params::new();
    b.iter(|| {
        let mut jobs = [
            blake2s_simd::many::HashManyJob::new(&params, input0.get()),
            blake2s_simd::many::HashManyJob::new(&params, input1.get()),
            blake2s_simd::many::HashManyJob::new(&params, input2.get()),
            blake2s_simd::many::HashManyJob::new(&params, input3.get()),
            blake2s_simd::many::HashManyJob::new(&params, input4.get()),
            blake2s_simd::many::HashManyJob::new(&params, input5.get()),
            blake2s_simd::many::HashManyJob::new(&params, input6.get()),
            blake2s_simd::many::HashManyJob::new(&params, input7.get()),
        ];
        blake2s_simd::many::hash_many(jobs.iter_mut());
        [
            jobs[0].to_hash(),
            jobs[1].to_hash(),
            jobs[2].to_hash(),
            jobs[3].to_hash(),
            jobs[4].to_hash(),
            jobs[5].to_hash(),
            jobs[6].to_hash(),
            jobs[7].to_hash(),
        ]
    });
}

// Note for comparison: The blake2-avx2-sneves C code is currently compiled
// with `clang -mavx2`. That is, not with -march=native. Upstream uses
// -march=native, but -mavx2 is closer to how blake2b_simd is compiled, and it
// makes the benchmark more apples-to-apples. When I compare compilers, GCC
// seems to produce better code than clang under -mavx2, but Clang seems to
// produce better code under -march=native. Not sure why.
#[cfg(feature = "blake2-avx2-sneves")]
#[bench]
fn bench_long_sneves_blake2b(b: &mut Bencher) {
    let mut input = RandomInput::new(b, LONG);
    b.iter(|| blake2_avx2_sneves::blake2b(input.get()));
}

#[cfg(feature = "blake2-avx2-sneves")]
#[bench]
fn bench_long_sneves_blake2bp(b: &mut Bencher) {
    let mut input = RandomInput::new(b, LONG);
    b.iter(|| blake2_avx2_sneves::blake2bp(input.get()));
}

#[cfg(feature = "blake2-avx2-sneves")]
#[bench]
fn bench_long_sneves_blake2sp(b: &mut Bencher) {
    let mut input = RandomInput::new(b, LONG);
    b.iter(|| blake2_avx2_sneves::blake2sp(input.get()));
}

// Note for comparison: Unlike the blake2-avx2-sneves C code above, the
// KangarooTwelve C code *is* compiled with -march=native. Their build system
// is more involved than above, and I don't want to muck around with it.
// Current benchmarks are almost exactly on par with blake2b_simd, maybe just a
// hair faster, which is a surprising coincidence. However, with the equivalent
// flag RUSTFLAGS="-C target-cpu=native", blake2b_simd pulls ahead.
#[cfg(feature = "kangarootwelve")]
#[bench]
fn bench_verylong_kangarootwelve(b: &mut Bencher) {
    let mut input = RandomInput::new(b, VERYLONG);
    b.iter(|| kangarootwelve::kangarootwelve(input.get()));
}

#[cfg(feature = "kangarootwelve")]
#[bench]
fn bench_long_kangarootwelve(b: &mut Bencher) {
    let mut input = RandomInput::new(b, LONG);
    b.iter(|| kangarootwelve::kangarootwelve(input.get()));
}

#[cfg(feature = "kangarootwelve")]
#[bench]
fn bench_onebyte_kangarootwelve(b: &mut Bencher) {
    b.iter(|| kangarootwelve::kangarootwelve(b"x"));
}

#[cfg(feature = "libsodium-ffi")]
#[bench]
fn bench_long_libsodium_blake2b(b: &mut Bencher) {
    let mut input = RandomInput::new(b, LONG);
    let mut out = [0; 64];
    unsafe {
        let init_ret = libsodium_ffi::sodium_init();
        assert!(init_ret != -1);
    }
    b.iter(|| unsafe {
        let input_slice = input.get();
        libsodium_ffi::crypto_generichash(
            out.as_mut_ptr(),
            out.len(),
            input_slice.as_ptr(),
            input_slice.len() as u64,
            std::ptr::null(),
            0,
        );
    });
}

#[cfg(feature = "libsodium-ffi")]
#[bench]
fn bench_onebyte_libsodium_blake2b(b: &mut Bencher) {
    let mut out = [0; 64];
    unsafe {
        let init_ret = libsodium_ffi::sodium_init();
        assert!(init_ret != -1);
    }
    b.iter(|| unsafe {
        let input_slice = b"x";
        libsodium_ffi::crypto_generichash(
            out.as_mut_ptr(),
            out.len(),
            input_slice.as_ptr(),
            input_slice.len() as u64,
            std::ptr::null(),
            0,
        );
    });
}

#[cfg(feature = "libsodium-ffi")]
#[bench]
fn bench_long_libsodium_chacha20(b: &mut Bencher) {
    b.bytes = LONG as u64;
    let mut out = vec![0; LONG];
    let mut key = [0; libsodium_ffi::crypto_stream_chacha20_KEYBYTES];
    rand::thread_rng().fill_bytes(&mut key);
    let mut nonce = [0; libsodium_ffi::crypto_stream_chacha20_NONCEBYTES];
    rand::thread_rng().fill_bytes(&mut nonce);
    unsafe {
        let init_ret = libsodium_ffi::sodium_init();
        assert!(init_ret != -1);
    }
    b.iter(|| unsafe {
        libsodium_ffi::crypto_stream_chacha20(
            out.as_mut_ptr(),
            out.len() as u64,
            nonce.as_ptr(),
            key.as_ptr(),
        );
    });
}

#[cfg(feature = "libsodium-ffi")]
#[bench]
fn bench_onebyte_libsodium_chacha20(b: &mut Bencher) {
    let mut out = [0];
    let mut key = [0; libsodium_ffi::crypto_stream_chacha20_KEYBYTES];
    rand::thread_rng().fill_bytes(&mut key);
    let mut nonce = [0; libsodium_ffi::crypto_stream_chacha20_NONCEBYTES];
    rand::thread_rng().fill_bytes(&mut nonce);
    unsafe {
        let init_ret = libsodium_ffi::sodium_init();
        assert!(init_ret != -1);
    }
    b.iter(|| unsafe {
        libsodium_ffi::crypto_stream_chacha20(
            out.as_mut_ptr(),
            out.len() as u64,
            nonce.as_ptr(),
            key.as_ptr(),
        );
    });
}

#[cfg(feature = "libsodium-ffi")]
#[bench]
fn bench_long_libsodium_poly1305(b: &mut Bencher) {
    let mut input = RandomInput::new(b, LONG);
    let mut out = [0; libsodium_ffi::crypto_onetimeauth_BYTES];
    let mut key = [0; libsodium_ffi::crypto_onetimeauth_KEYBYTES];
    rand::thread_rng().fill_bytes(&mut key);
    unsafe {
        let init_ret = libsodium_ffi::sodium_init();
        assert!(init_ret != -1);
    }
    b.iter(|| unsafe {
        let input_slice = input.get();
        libsodium_ffi::crypto_onetimeauth(
            out.as_mut_ptr(),
            input_slice.as_ptr(),
            input_slice.len() as u64,
            key.as_ptr(),
        );
    });
}

#[cfg(feature = "libsodium-ffi")]
#[bench]
fn bench_onebyte_libsodium_poly1305(b: &mut Bencher) {
    let mut out = [0; libsodium_ffi::crypto_onetimeauth_BYTES];
    let mut key = [0; libsodium_ffi::crypto_onetimeauth_KEYBYTES];
    rand::thread_rng().fill_bytes(&mut key);
    unsafe {
        let init_ret = libsodium_ffi::sodium_init();
        assert!(init_ret != -1);
    }
    b.iter(|| unsafe {
        let input_slice = b"x";
        libsodium_ffi::crypto_onetimeauth(
            out.as_mut_ptr(),
            input_slice.as_ptr(),
            input_slice.len() as u64,
            key.as_ptr(),
        );
    });
}

#[cfg(feature = "openssl")]
#[bench]
fn bench_long_openssl_md5(b: &mut Bencher) {
    let mut input = RandomInput::new(b, LONG);
    b.iter(|| openssl::hash::hash(openssl::hash::MessageDigest::md5(), input.get()));
}

#[cfg(feature = "openssl")]
#[bench]
fn bench_onebyte_openssl_md5(b: &mut Bencher) {
    b.iter(|| openssl::hash::hash(openssl::hash::MessageDigest::md5(), b"x"));
}

#[cfg(feature = "openssl")]
#[bench]
fn bench_long_openssl_sha1(b: &mut Bencher) {
    let mut input = RandomInput::new(b, LONG);
    b.iter(|| openssl::hash::hash(openssl::hash::MessageDigest::sha1(), input.get()));
}

#[cfg(feature = "openssl")]
#[bench]
fn bench_onebyte_openssl_sha1(b: &mut Bencher) {
    b.iter(|| openssl::hash::hash(openssl::hash::MessageDigest::sha1(), b"x"));
}

#[cfg(feature = "openssl")]
#[bench]
fn bench_long_openssl_sha256(b: &mut Bencher) {
    let mut input = RandomInput::new(b, LONG);
    b.iter(|| openssl::hash::hash(openssl::hash::MessageDigest::sha256(), input.get()));
}

#[cfg(feature = "openssl")]
#[bench]
fn bench_onebyte_openssl_sha256(b: &mut Bencher) {
    b.iter(|| openssl::hash::hash(openssl::hash::MessageDigest::sha256(), b"x"));
}

#[cfg(feature = "openssl")]
#[bench]
fn bench_long_openssl_sha512(b: &mut Bencher) {
    let mut input = RandomInput::new(b, LONG);
    b.iter(|| openssl::hash::hash(openssl::hash::MessageDigest::sha512(), input.get()));
}

#[cfg(feature = "openssl")]
#[bench]
fn bench_onebyte_openssl_sha3_256(b: &mut Bencher) {
    b.iter(|| openssl::hash::hash(openssl::hash::MessageDigest::sha3_256(), b"x"));
}

#[cfg(feature = "openssl")]
#[bench]
fn bench_long_openssl_sha3_256(b: &mut Bencher) {
    let mut input = RandomInput::new(b, LONG);
    b.iter(|| openssl::hash::hash(openssl::hash::MessageDigest::sha3_256(), input.get()));
}

#[cfg(feature = "openssl")]
#[bench]
fn bench_onebyte_openssl_sha512(b: &mut Bencher) {
    b.iter(|| openssl::hash::hash(openssl::hash::MessageDigest::sha512(), b"x"));
}

#[cfg(feature = "ring")]
#[bench]
fn bench_long_ring_sha1(b: &mut Bencher) {
    let mut input = RandomInput::new(b, LONG);
    b.iter(|| ring::digest::digest(&ring::digest::SHA1_FOR_LEGACY_USE_ONLY, input.get()));
}

#[cfg(feature = "ring")]
#[bench]
fn bench_onebyte_ring_sha1(b: &mut Bencher) {
    b.iter(|| ring::digest::digest(&ring::digest::SHA1_FOR_LEGACY_USE_ONLY, b"x"));
}

#[cfg(feature = "ring")]
#[bench]
fn bench_long_ring_sha256(b: &mut Bencher) {
    let mut input = RandomInput::new(b, LONG);
    b.iter(|| ring::digest::digest(&ring::digest::SHA256, input.get()));
}

#[cfg(feature = "ring")]
#[bench]
fn bench_onebyte_ring_sha256(b: &mut Bencher) {
    b.iter(|| ring::digest::digest(&ring::digest::SHA256, b"x"));
}

#[cfg(feature = "ring")]
#[bench]
fn bench_long_ring_sha512(b: &mut Bencher) {
    let mut input = RandomInput::new(b, LONG);
    b.iter(|| ring::digest::digest(&ring::digest::SHA512, input.get()));
}

#[cfg(feature = "ring")]
#[bench]
fn bench_onebyte_ring_sha512(b: &mut Bencher) {
    b.iter(|| ring::digest::digest(&ring::digest::SHA512, b"x"));
}

#[cfg(feature = "ring")]
#[bench]
fn bench_long_ring_chacha20poly1305(b: &mut Bencher) {
    let mut input = RandomInput::new(b, LONG);
    let mut buf = input.get().to_vec();
    let alg = &ring::aead::CHACHA20_POLY1305;
    let mut key_bytes = vec![0; alg.key_len()];
    rand::thread_rng().fill_bytes(&mut key_bytes);
    let unbound_key = ring::aead::UnboundKey::new(alg, &key_bytes).expect("invalid key");
    let less_safe_key = ring::aead::LessSafeKey::new(unbound_key);
    let mut nonce_bytes = vec![0; alg.nonce_len()];
    rand::thread_rng().fill_bytes(&mut nonce_bytes);
    b.iter(|| {
        let nonce =
            ring::aead::Nonce::try_assume_unique_for_key(&nonce_bytes).expect("invalid nonce");
        less_safe_key
            .seal_in_place_separate_tag(nonce, ring::aead::Aad::empty(), &mut buf)
            .expect("invalid encryption")
    });
}

#[cfg(feature = "ring")]
#[bench]
fn bench_onebyte_ring_chacha20poly1305(b: &mut Bencher) {
    let mut buf = [0];
    let alg = &ring::aead::CHACHA20_POLY1305;
    let mut key_bytes = vec![0; alg.key_len()];
    rand::thread_rng().fill_bytes(&mut key_bytes);
    let unbound_key = ring::aead::UnboundKey::new(alg, &key_bytes).expect("invalid key");
    let less_safe_key = ring::aead::LessSafeKey::new(unbound_key);
    let mut nonce_bytes = vec![0; alg.nonce_len()];
    rand::thread_rng().fill_bytes(&mut nonce_bytes);
    b.iter(|| {
        let nonce =
            ring::aead::Nonce::try_assume_unique_for_key(&nonce_bytes).expect("invalid nonce");
        less_safe_key
            .seal_in_place_separate_tag(nonce, ring::aead::Aad::empty(), &mut buf)
            .expect("invalid encryption")
    });
}
