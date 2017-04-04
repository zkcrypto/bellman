extern crate bincode;

use curves::*;
use super::*;

fn test_vectors<E: Engine, G: Group<E>>(e: &E, expected: &[u8]) {
    let mut bytes = vec![];
    let mut acc = G::zero(e);
    let mut expected_reader = expected;

    for _ in 0..10000 {
        {
            let acc = acc.to_affine(e);
            let exp: <G::Affine as GroupAffine<E, G>>::Uncompressed =
                bincode::deserialize_from(&mut expected_reader, bincode::Infinite).unwrap();

            assert!(acc == exp.to_affine(e).unwrap());

            let acc = acc.to_uncompressed(e);
            bincode::serialize_into(&mut bytes, &acc, bincode::Infinite).unwrap();
        }
        acc.double(e);
        acc.add_assign(e, &G::one(e));
    }

    assert_eq!(&bytes[..], expected);
}

#[test]
fn g1_serialization_test_vectors() {
    let engine = Bls381::new();

    test_vectors::<Bls381, G1>(&engine, include_bytes!("g1_serialized.bin"));
}

#[test]
fn g2_serialization_test_vectors() {
    let engine = Bls381::new();

    test_vectors::<Bls381, G2>(&engine, include_bytes!("g2_serialized.bin"));
}
