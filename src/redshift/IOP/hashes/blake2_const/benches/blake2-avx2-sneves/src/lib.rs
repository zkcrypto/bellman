pub fn blake2b(input: &[u8]) -> [u8; 64] {
    check_avx2();
    let mut hash = [0u8; 64];
    unsafe {
        sys::blake2b(hash.as_mut_ptr(), input.as_ptr(), input.len());
    }
    hash
}

pub fn blake2bp(input: &[u8]) -> [u8; 64] {
    check_avx2();
    let mut hash = [0u8; 64];
    unsafe {
        sys::blake2bp(hash.as_mut_ptr(), input.as_ptr(), input.len());
    }
    hash
}

pub fn blake2sp(input: &[u8]) -> [u8; 32] {
    check_avx2();
    let mut hash = [0u8; 32];
    unsafe {
        sys::blake2sp(hash.as_mut_ptr(), input.as_ptr(), input.len());
    }
    hash
}

fn check_avx2() {
    if !is_x86_feature_detected!("avx2") {
        panic!("AVX2 support is missing")
    }
}

mod sys {
    extern "C" {
        pub fn blake2b(
            out: *mut ::std::os::raw::c_uchar,
            in_: *const ::std::os::raw::c_uchar,
            inlen: usize,
        ) -> ::std::os::raw::c_int;

        pub fn blake2bp(
            out: *mut ::std::os::raw::c_uchar,
            in_: *const ::std::os::raw::c_uchar,
            inlen: usize,
        ) -> ::std::os::raw::c_int;

        pub fn blake2sp(
            out: *mut ::std::os::raw::c_uchar,
            in_: *const ::std::os::raw::c_uchar,
            inlen: usize,
        ) -> ::std::os::raw::c_int;
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use serde::{Deserialize, Serialize};

    #[derive(Debug, Serialize, Deserialize)]
    struct TestCase {
        hash: String,
        #[serde(rename = "in")]
        in_: String,
        key: String,
        out: String,
    }

    #[test]
    fn test_vectors() {
        let test_cases: Vec<TestCase> =
            serde_json::from_str(include_str!("../../../tests/blake2-kat.json")).unwrap();
        let mut num = 0;
        for case in &test_cases {
            let input = hex::decode(&case.in_).unwrap();
            let output = hex::decode(&case.out).unwrap();
            if !case.key.is_empty() {
                // These implementations don't have a key parameter.
                continue;
            }
            let mut found = Vec::new();
            match case.hash.as_str() {
                "blake2b" => found.extend_from_slice(&blake2b(&input)),
                "blake2bp" => found.extend_from_slice(&blake2bp(&input)),
                "blake2sp" => found.extend_from_slice(&blake2sp(&input)),
                _ => continue, // other hashes not implemented
            };
            dbg!(case);
            assert_eq!(output, found);
            num += 1;
        }
        assert_eq!(
            768, num,
            "make sure we don't accidentally stop running tests"
        );
    }
}
