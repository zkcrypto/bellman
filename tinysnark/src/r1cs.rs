use libc::{size_t};
use super::arith::FieldT;

#[repr(C)]
struct R1ConstraintSystem;

#[repr(C)]
pub struct LinearTerm {
    pub coeff: FieldT,
    pub index: size_t
}

extern "C" {
    fn tinysnark_new_r1cs(primary: size_t, aux: size_t) -> *mut R1ConstraintSystem;
    fn tinysnark_drop_r1cs(cs: *mut R1ConstraintSystem);
    fn tinysnark_satisfy_test(cs: *mut R1ConstraintSystem, primary: *const FieldT, aux: *const FieldT) -> bool;
    fn tinysnark_add_constraint(cs: *mut R1ConstraintSystem,
                                a: *const LinearTerm,
                                a_len: size_t,
                                b: *const LinearTerm,
                                b_len: size_t,
                                c: *const LinearTerm,
                                c_len: size_t
                               );
}

pub struct ConstraintSystem {
    cs: *mut R1ConstraintSystem,
    primary_size: usize,
    aux_size: usize
}

impl Drop for ConstraintSystem {
    fn drop(&mut self) {
        unsafe { tinysnark_drop_r1cs(self.cs) }
    }
}

impl ConstraintSystem {
    pub fn new(primary_size: usize, aux_size: usize) -> ConstraintSystem {
        ConstraintSystem {
            cs: unsafe { tinysnark_new_r1cs(primary_size, aux_size) },
            primary_size: primary_size,
            aux_size: aux_size
        }
    }

    pub fn add_constraint(&mut self, a: &[LinearTerm], b: &[LinearTerm], c: &[LinearTerm])
    {
        unsafe {
            tinysnark_add_constraint(
                self.cs,
                a.get_unchecked(0),
                a.len(),
                b.get_unchecked(0),
                b.len(),
                c.get_unchecked(0),
                c.len()
            );
        }
    }

    pub fn test(&mut self, primary: &[FieldT], aux: &[FieldT]) -> bool
    {
        assert_eq!(primary.len(), self.primary_size);
        assert_eq!(aux.len(), self.aux_size);
        
        unsafe {
            tinysnark_satisfy_test(self.cs, primary.get_unchecked(0), aux.get_unchecked(0))
        }
    }
}

#[repr(C)]
struct R1CSKeypair;

pub struct Keypair {
    kp: *mut R1CSKeypair,
    primary_size: usize,
    aux_size: usize
}

impl Keypair {
    pub fn new(constraint_system: &ConstraintSystem) -> Keypair {
        Keypair {
            kp: unsafe { tinysnark_gen_keypair(constraint_system.cs) },
            primary_size: constraint_system.primary_size,
            aux_size: constraint_system.aux_size
        }
    }
}

impl Drop for Keypair {
    fn drop(&mut self) {
        unsafe { tinysnark_drop_keypair(self.kp) }
    }
}

extern "C" {
    fn tinysnark_gen_keypair(cs: *mut R1ConstraintSystem) -> *mut R1CSKeypair;
    fn tinysnark_drop_keypair(cs: *mut R1CSKeypair);
}

#[repr(C)]
struct R1CSProof;

pub struct Proof {
    proof: *mut R1CSProof
}

impl Proof {
    pub fn new(keypair: &Keypair, primary: &[FieldT], aux: &[FieldT])
        -> Proof
    {
        assert_eq!(primary.len(), keypair.primary_size);
        assert_eq!(aux.len(), keypair.aux_size);

        unsafe {
            Proof {
                proof: tinysnark_gen_proof(keypair.kp, primary.get_unchecked(0), aux.get_unchecked(0))
            }
        }
    }

    pub fn verify(&self, keypair: &Keypair, primary: &[FieldT]) -> bool {
        assert_eq!(primary.len(), keypair.primary_size);

        unsafe {
            tinysnark_verify_proof(self.proof, keypair.kp, primary.get_unchecked(0))
        }
    }
}

impl Drop for Proof {
    fn drop(&mut self) {
        unsafe { tinysnark_drop_proof(self.proof) }
    }
}

extern "C" {
    fn tinysnark_gen_proof(keypair: *mut R1CSKeypair,
                           primary: *const FieldT,
                           aux: *const FieldT) -> *mut R1CSProof;
    fn tinysnark_verify_proof(proof: *mut R1CSProof,
                              keypair: *mut R1CSKeypair,
                              primary: *const FieldT) -> bool;
    fn tinysnark_drop_proof(proof: *mut R1CSProof);
}