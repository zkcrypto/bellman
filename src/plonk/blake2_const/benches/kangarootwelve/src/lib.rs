pub fn kangarootwelve(input: &[u8]) -> [u8; 32] {
    let mut hash = [0u8; 32];
    let ret = unsafe {
        KangarooTwelve(
            input.as_ptr(),
            input.len(),
            hash.as_mut_ptr(),
            hash.len(),
            std::ptr::null(),
            0,
        )
    };
    debug_assert_eq!(0, ret, "KangarooTwelve returned an error code");
    hash
}

extern "C" {
    #[doc = " Extendable ouput function KangarooTwelve."]
    #[doc = " @param  input           Pointer to the input message (M)."]
    #[doc = " @param  inputByteLen    The length of the input message in bytes."]
    #[doc = " @param  output          Pointer to the output buffer."]
    #[doc = " @param  outputByteLen   The desired number of output bytes."]
    #[doc = " @param  customization   Pointer to the customization string (C)."]
    #[doc = " @param  customByteLen   The length of the customization string in bytes."]
    #[doc = " @return 0 if successful, 1 otherwise."]
    fn KangarooTwelve(
        input: *const ::std::os::raw::c_uchar,
        inputByteLen: usize,
        output: *mut ::std::os::raw::c_uchar,
        outputByteLen: usize,
        customization: *const ::std::os::raw::c_uchar,
        customByteLen: usize,
    ) -> ::std::os::raw::c_int;
}

#[cfg(test)]
mod test {
    use super::*;

    // from https://eprint.iacr.org/2016/770.pdf
    #[test]
    fn test_vectors() {
        let empty_expected = "1ac2d450fc3b4205d19da7bfca1b37513c0803577ac7167f06fe2ce1f0ef39e5";
        let empty_output = kangarootwelve(&[]);
        assert_eq!(empty_expected, hex::encode(&empty_output));

        let seventeen_expected = "6bf75fa2239198db4772e36478f8e19b0f371205f6a9a93a273f51df37122888";
        let mut input = Vec::new();
        for i in 0..17u8 {
            input.push(i);
        }
        let seventeen_output = kangarootwelve(&input);
        assert_eq!(seventeen_expected, hex::encode(&seventeen_output));
    }
}
