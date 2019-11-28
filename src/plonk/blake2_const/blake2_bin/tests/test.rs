use duct::cmd;
use std::io::prelude::*;
use std::path::PathBuf;
use tempfile::NamedTempFile;

pub fn blake2_exe() -> PathBuf {
    assert_cmd::cargo::cargo_bin("blake2")
}

#[test]
fn test_stdin() {
    let output = cmd!(blake2_exe(), "--length=16")
        .stdin_bytes("abcdef")
        .read()
        .expect("blake2 failed");
    assert_eq!("2465e7ee63a17b4b307c7792c432aef6", output);
}

#[test]
fn test_input_file() {
    let mut file = NamedTempFile::new().unwrap();
    file.write_all("abcdef".as_bytes()).unwrap();
    file.flush().unwrap();
    let output = cmd!(blake2_exe(), "--length=16", file.path())
        .read()
        .expect("blake2 failed");
    assert_eq!("2465e7ee63a17b4b307c7792c432aef6", output);
}

#[test]
fn test_input_file_mmap() {
    let mut file = NamedTempFile::new().unwrap();
    file.write_all("abcdef".as_bytes()).unwrap();
    file.flush().unwrap();
    let output = cmd!(blake2_exe(), "--length=16", "--mmap", file.path())
        .read()
        .expect("blake2 failed");
    assert_eq!("2465e7ee63a17b4b307c7792c432aef6", output);
}

#[test]
fn test_blake2bp() {
    // From https://raw.githubusercontent.com/BLAKE2/BLAKE2/master/testvectors/blake2-kat.json.
    let vectors: &[(&[u8], &str)] = &[
        (
            b"",
            "b5ef811a8038f70b628fa8b294daae7492b1ebe343a80eaabbf1f6ae664dd67b\
             9d90b0120791eab81dc96985f28849f6a305186a85501b405114bfa678df9380",
        ),
        (
            b"\x00",
            "a139280e72757b723e6473d5be59f36e9d50fc5cd7d4585cbc09804895a36c52\
             1242fb2789f85cb9e35491f31d4a6952f9d8e097aef94fa1ca0b12525721f03d",
        ),
        (
            b"\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f\
              \x10\x11\x12\x13\x14\x15\x16\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f\
              \x20\x21\x22\x23\x24\x25\x26\x27\x28\x29\x2a\x2b\x2c\x2d\x2e\x2f\
              \x30\x31\x32\x33\x34\x35\x36\x37\x38\x39\x3a\x3b\x3c\x3d\x3e\x3f\
              \x40\x41\x42\x43\x44\x45\x46\x47\x48\x49\x4a\x4b\x4c\x4d\x4e\x4f\
              \x50\x51\x52\x53\x54\x55\x56\x57\x58\x59\x5a\x5b\x5c\x5d\x5e\x5f\
              \x60\x61\x62\x63\x64\x65\x66\x67\x68\x69\x6a\x6b\x6c\x6d\x6e\x6f\
              \x70\x71\x72\x73\x74\x75\x76\x77\x78\x79\x7a\x7b\x7c\x7d\x7e\x7f\
              \x80\x81\x82\x83\x84\x85\x86\x87\x88\x89\x8a\x8b\x8c\x8d\x8e\x8f\
              \x90\x91\x92\x93\x94\x95\x96\x97\x98\x99\x9a\x9b\x9c\x9d\x9e\x9f\
              \xa0\xa1\xa2\xa3\xa4\xa5\xa6\xa7\xa8\xa9\xaa\xab\xac\xad\xae\xaf\
              \xb0\xb1\xb2\xb3\xb4\xb5\xb6\xb7\xb8\xb9\xba\xbb\xbc\xbd\xbe\xbf\
              \xc0\xc1\xc2\xc3\xc4\xc5\xc6\xc7\xc8\xc9\xca\xcb\xcc\xcd\xce\xcf\
              \xd0\xd1\xd2\xd3\xd4\xd5\xd6\xd7\xd8\xd9\xda\xdb\xdc\xdd\xde\xdf\
              \xe0\xe1\xe2\xe3\xe4\xe5\xe6\xe7\xe8\xe9\xea\xeb\xec\xed\xee\xef\
              \xf0\xf1\xf2\xf3\xf4\xf5\xf6\xf7\xf8\xf9\xfa\xfb\xfc\xfd\xfe",
            "3f35c45d24fcfb4acca651076c08000e279ebbff37a1333ce19fd577202dbd24\
             b58c514e36dd9ba64af4d78eea4e2dd13bc18d798887dd971376bcae0087e17e",
        ),
    ];

    for &(input, expected) in vectors {
        let mut file = NamedTempFile::new().unwrap();
        file.write_all(input).unwrap();
        file.flush().unwrap();

        let output = cmd!(blake2_exe(), "-bp", file.path())
            .read()
            .expect("blake2 failed");
        assert_eq!(expected, output);
    }
}

#[test]
fn test_last_node_flag() {
    let output = cmd!(blake2_exe(), "--length=16", "--last-node")
        .stdin_bytes("abcdef")
        .read()
        .expect("blake2 failed");
    assert_eq!("d788eeea837a3d10b1f8c097059f815a", output);
}

// This is the exact same result as test_all_parameters in the library tests.
#[test]
fn test_all_parameters_blake2b() {
    let flags = [
        "-b",
        "--length=18",
        "--key=626172",
        "--salt=62617a62617a62617a62617a62617a62",
        "--personal=62696e672062696e672062696e672062",
        "--fanout=2",
        "--max-depth=3",
        "--max-leaf-length=67438087",
        "--node-offset=579005069656919567",
        "--node-depth=16",
        "--inner-hash-length=17",
        "--last-node",
    ];
    let output = cmd(blake2_exe(), flags.iter())
        .stdin_bytes("foo")
        .read()
        .expect("blake2 failed");
    assert_eq!("ec0f59cb65f92e7fcca1280ba859a6925ded", output);
}

// This is the exact same result as test_all_parameters in the library tests.
#[test]
fn test_all_parameters_blake2s() {
    let flags = [
        "-s",
        "--length=18",
        "--key=626172",
        "--salt=62617a62617a6261",
        "--personal=62696e672062696e",
        "--fanout=2",
        "--max-depth=3",
        "--max-leaf-length=67438087",
        "--node-offset=8834916224013",
        "--node-depth=16",
        "--inner-hash-length=17",
        "--last-node",
    ];
    let output = cmd(blake2_exe(), flags.iter())
        .stdin_bytes("foo")
        .read()
        .expect("blake2 failed");
    assert_eq!("62361e5392ab0eb7dd27e48a6809ee82dc57", output);
}

// This is the exact same result as test_all_parameters_blake2bp in the library tests.
#[test]
fn test_all_parameters_blake2bp() {
    let flags = ["-bp", "--length=18", "--key=626172"];
    let output = cmd(blake2_exe(), flags.iter())
        .stdin_bytes("foo")
        .read()
        .expect("blake2 failed");
    assert_eq!("8c54e888a8a01c63da6585c058fe54ea81df", output);
}

// This is the exact same result as test_all_parameters_blake2sp in the library tests.
#[test]
fn test_all_parameters_blake2sp() {
    let flags = ["-sp", "--length=18", "--key=626172"];
    let output = cmd(blake2_exe(), flags.iter())
        .stdin_bytes("foo")
        .read()
        .expect("blake2 failed");
    assert_eq!("947d4c671e2794f5e1a57daeca97bb46ed66", output);
}
