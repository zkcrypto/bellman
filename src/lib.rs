//! `bellman` is a crate for building zk-SNARK circuits. It provides circuit
//! traits and and primitive structures, as well as basic gadget implementations
//! such as booleans and number abstractions.
//!
//! # Example circuit
//!
//! Say we want to write a circuit that proves we know the preimage to some hash
//! computed using SHA-256d (calling SHA-256 twice). The preimage must have a
//! fixed length known in advance (because the circuit parameters will depend on
//! it), but can otherwise have any value. We take the following strategy:
//!
//! - Witness each bit of the preimage.
//! - Compute `hash = SHA-256d(preimage)` inside the circuit.
//! - Expose `hash` as a public input using multiscalar packing.
//!
//! ```
//! use bellman::{
//!     gadgets::{
//!         boolean::{AllocatedBit, Boolean},
//!         multipack,
//!         sha256::sha256,
//!     },
//!     groth16, Circuit, ConstraintSystem, SynthesisError,
//! };
//! use bls12_381::Bls12;
//! use ff::PrimeField;
//! use pairing::Engine;
//! use rand::rngs::OsRng;
//! use sha2::{Digest, Sha256};
//!
//! /// Our own SHA-256d gadget. Input and output are in little-endian bit order.
//! fn sha256d<Scalar: PrimeField, CS: ConstraintSystem<Scalar>>(
//!     mut cs: CS,
//!     data: &[Boolean],
//! ) -> Result<Vec<Boolean>, SynthesisError> {
//!     // Flip endianness of each input byte
//!     let input: Vec<_> = data
//!         .chunks(8)
//!         .map(|c| c.iter().rev())
//!         .flatten()
//!         .cloned()
//!         .collect();
//!
//!     let mid = sha256(cs.namespace(|| "SHA-256(input)"), &input)?;
//!     let res = sha256(cs.namespace(|| "SHA-256(mid)"), &mid)?;
//!
//!     // Flip endianness of each output byte
//!     Ok(res
//!         .chunks(8)
//!         .map(|c| c.iter().rev())
//!         .flatten()
//!         .cloned()
//!         .collect())
//! }
//!
//! struct MyCircuit {
//!     /// The input to SHA-256d we are proving that we know. Set to `None` when we
//!     /// are verifying a proof (and do not have the witness data).
//!     preimage: Option<[u8; 80]>,
//! }
//!
//! impl<Scalar: PrimeField> Circuit<Scalar> for MyCircuit {
//!     fn synthesize<CS: ConstraintSystem<Scalar>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
//!         // Compute the values for the bits of the preimage. If we are verifying a proof,
//!         // we still need to create the same constraints, so we return an equivalent-size
//!         // Vec of None (indicating that the value of each bit is unknown).
//!         let bit_values = if let Some(preimage) = self.preimage {
//!             preimage
//!                 .into_iter()
//!                 .map(|byte| (0..8).map(move |i| (byte >> i) & 1u8 == 1u8))
//!                 .flatten()
//!                 .map(|b| Some(b))
//!                 .collect()
//!         } else {
//!             vec![None; 80 * 8]
//!         };
//!         assert_eq!(bit_values.len(), 80 * 8);
//!
//!         // Witness the bits of the preimage.
//!         let preimage_bits = bit_values
//!             .into_iter()
//!             .enumerate()
//!             // Allocate each bit.
//!             .map(|(i, b)| {
//!                 AllocatedBit::alloc(cs.namespace(|| format!("preimage bit {}", i)), b)
//!             })
//!             // Convert the AllocatedBits into Booleans (required for the sha256 gadget).
//!             .map(|b| b.map(Boolean::from))
//!             .collect::<Result<Vec<_>, _>>()?;
//!
//!         // Compute hash = SHA-256d(preimage).
//!         let hash = sha256d(cs.namespace(|| "SHA-256d(preimage)"), &preimage_bits)?;
//!
//!         // Expose the vector of 32 boolean variables as compact public inputs.
//!         multipack::pack_into_inputs(cs.namespace(|| "pack hash"), &hash)
//!     }
//! }
//!
//! // Create parameters for our circuit. In a production deployment these would
//! // be generated securely using a multiparty computation.
//! let params = {
//!     let c = MyCircuit { preimage: None };
//!     groth16::generate_random_parameters::<Bls12, _, _>(c, &mut OsRng).unwrap()
//! };
//!
//! // Prepare the verification key (for proof verification).
//! let pvk = groth16::prepare_verifying_key(&params.vk);
//!
//! // Pick a preimage and compute its hash.
//! let preimage = [42; 80];
//! let hash = Sha256::digest(&Sha256::digest(&preimage));
//!
//! // Create an instance of our circuit (with the preimage as a witness).
//! let c = MyCircuit {
//!     preimage: Some(preimage),
//! };
//!
//! // Create a Groth16 proof with our parameters.
//! let proof = groth16::create_random_proof(c, &params, &mut OsRng).unwrap();
//!
//! // Pack the hash as inputs for proof verification.
//! let hash_bits = multipack::bytes_to_bits_le(&hash);
//! let inputs = multipack::compute_multipacking(&hash_bits);
//!
//! // Check the proof!
//! assert!(groth16::verify_proof(&pvk, &proof, &inputs).is_ok());
//! ```
//!
//! # Roadmap
//!
//! `bellman` is being refactored into a generic proving library. Currently it
//! is pairing-specific, and different types of proving systems need to be
//! implemented as sub-modules. After the refactor, `bellman` will be generic
//! using the [`ff`] and [`group`] crates, while specific proving systems will
//! be separate crates that pull in the dependencies they require.

// Catch documentation errors caused by code changes.
#![deny(intra_doc_link_resolution_failure)]

pub mod domain;
pub mod gadgets;
#[cfg(feature = "groth16")]
pub mod groth16;
pub mod multicore;
mod multiexp;

use ff::PrimeField;

use std::error::Error;
use std::fmt;
use std::io;
use std::marker::PhantomData;
use std::ops::{Add, Sub};

/// Computations are expressed in terms of arithmetic circuits, in particular
/// rank-1 quadratic constraint systems. The `Circuit` trait represents a
/// circuit that can be synthesized. The `synthesize` method is called during
/// CRS generation and during proving.
pub trait Circuit<Scalar: PrimeField> {
    /// Synthesize the circuit into a rank-1 quadratic constraint system
    fn synthesize<CS: ConstraintSystem<Scalar>>(self, cs: &mut CS) -> Result<(), SynthesisError>;
}

/// Represents a variable in our constraint system.
#[derive(Copy, Clone, Debug)]
pub struct Variable(Index);

impl Variable {
    /// This constructs a variable with an arbitrary index.
    /// Circuit implementations are not recommended to use this.
    pub fn new_unchecked(idx: Index) -> Variable {
        Variable(idx)
    }

    /// This returns the index underlying the variable.
    /// Circuit implementations are not recommended to use this.
    pub fn get_unchecked(&self) -> Index {
        self.0
    }
}

/// Represents the index of either an input variable or
/// auxiliary variable.
#[derive(Copy, Clone, PartialEq, Debug)]
pub enum Index {
    Input(usize),
    Aux(usize),
}

/// This represents a linear combination of some variables, with coefficients
/// in the scalar field of a pairing-friendly elliptic curve group.
#[derive(Clone)]
pub struct LinearCombination<Scalar: PrimeField>(Vec<(Variable, Scalar)>);

impl<Scalar: PrimeField> AsRef<[(Variable, Scalar)]> for LinearCombination<Scalar> {
    fn as_ref(&self) -> &[(Variable, Scalar)] {
        &self.0
    }
}

impl<Scalar: PrimeField> LinearCombination<Scalar> {
    pub fn zero() -> LinearCombination<Scalar> {
        LinearCombination(vec![])
    }
}

impl<Scalar: PrimeField> Add<(Scalar, Variable)> for LinearCombination<Scalar> {
    type Output = LinearCombination<Scalar>;

    fn add(mut self, (coeff, var): (Scalar, Variable)) -> LinearCombination<Scalar> {
        self.0.push((var, coeff));

        self
    }
}

impl<Scalar: PrimeField> Sub<(Scalar, Variable)> for LinearCombination<Scalar> {
    type Output = LinearCombination<Scalar>;

    #[allow(clippy::suspicious_arithmetic_impl)]
    fn sub(self, (coeff, var): (Scalar, Variable)) -> LinearCombination<Scalar> {
        self + (coeff.neg(), var)
    }
}

impl<Scalar: PrimeField> Add<Variable> for LinearCombination<Scalar> {
    type Output = LinearCombination<Scalar>;

    fn add(self, other: Variable) -> LinearCombination<Scalar> {
        self + (Scalar::one(), other)
    }
}

impl<Scalar: PrimeField> Sub<Variable> for LinearCombination<Scalar> {
    type Output = LinearCombination<Scalar>;

    fn sub(self, other: Variable) -> LinearCombination<Scalar> {
        self - (Scalar::one(), other)
    }
}

impl<'a, Scalar: PrimeField> Add<&'a LinearCombination<Scalar>> for LinearCombination<Scalar> {
    type Output = LinearCombination<Scalar>;

    fn add(mut self, other: &'a LinearCombination<Scalar>) -> LinearCombination<Scalar> {
        for s in &other.0 {
            self = self + (s.1, s.0);
        }

        self
    }
}

impl<'a, Scalar: PrimeField> Sub<&'a LinearCombination<Scalar>> for LinearCombination<Scalar> {
    type Output = LinearCombination<Scalar>;

    fn sub(mut self, other: &'a LinearCombination<Scalar>) -> LinearCombination<Scalar> {
        for s in &other.0 {
            self = self - (s.1, s.0);
        }

        self
    }
}

impl<'a, Scalar: PrimeField> Add<(Scalar, &'a LinearCombination<Scalar>)>
    for LinearCombination<Scalar>
{
    type Output = LinearCombination<Scalar>;

    fn add(
        mut self,
        (coeff, other): (Scalar, &'a LinearCombination<Scalar>),
    ) -> LinearCombination<Scalar> {
        for s in &other.0 {
            let mut tmp = s.1;
            tmp.mul_assign(&coeff);
            self = self + (tmp, s.0);
        }

        self
    }
}

impl<'a, Scalar: PrimeField> Sub<(Scalar, &'a LinearCombination<Scalar>)>
    for LinearCombination<Scalar>
{
    type Output = LinearCombination<Scalar>;

    fn sub(
        mut self,
        (coeff, other): (Scalar, &'a LinearCombination<Scalar>),
    ) -> LinearCombination<Scalar> {
        for s in &other.0 {
            let mut tmp = s.1;
            tmp.mul_assign(&coeff);
            self = self - (tmp, s.0);
        }

        self
    }
}

/// This is an error that could occur during circuit synthesis contexts,
/// such as CRS generation or proving.
#[derive(Debug)]
pub enum SynthesisError {
    /// During synthesis, we lacked knowledge of a variable assignment.
    AssignmentMissing,
    /// During synthesis, we divided by zero.
    DivisionByZero,
    /// During synthesis, we constructed an unsatisfiable constraint system.
    Unsatisfiable,
    /// During synthesis, our polynomials ended up being too high of degree
    PolynomialDegreeTooLarge,
    /// During proof generation, we encountered an identity in the CRS
    UnexpectedIdentity,
    /// During proof generation, we encountered an I/O error with the CRS
    IoError(io::Error),
    /// During CRS generation, we observed an unconstrained auxiliary variable
    UnconstrainedVariable,
}

impl From<io::Error> for SynthesisError {
    fn from(e: io::Error) -> SynthesisError {
        SynthesisError::IoError(e)
    }
}

impl Error for SynthesisError {
    fn description(&self) -> &str {
        match *self {
            SynthesisError::AssignmentMissing => {
                "an assignment for a variable could not be computed"
            }
            SynthesisError::DivisionByZero => "division by zero",
            SynthesisError::Unsatisfiable => "unsatisfiable constraint system",
            SynthesisError::PolynomialDegreeTooLarge => "polynomial degree is too large",
            SynthesisError::UnexpectedIdentity => "encountered an identity element in the CRS",
            SynthesisError::IoError(_) => "encountered an I/O error",
            SynthesisError::UnconstrainedVariable => "auxiliary variable was unconstrained",
        }
    }
}

impl fmt::Display for SynthesisError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        if let SynthesisError::IoError(ref e) = *self {
            write!(f, "I/O error: ")?;
            e.fmt(f)
        } else {
            write!(f, "{}", self)
        }
    }
}

/// An error during verification.
#[derive(Debug, Clone)]
pub enum VerificationError {
    /// Verification was attempted with a malformed verifying key.
    InvalidVerifyingKey,
    /// Proof verification failed.
    InvalidProof,
}

impl Error for VerificationError {
    fn description(&self) -> &str {
        match *self {
            VerificationError::InvalidVerifyingKey => "malformed verifying key",
            VerificationError::InvalidProof => "proof verification failed",
        }
    }
}

impl fmt::Display for VerificationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", self)
    }
}

/// Represents a constraint system which can have new variables
/// allocated and constrains between them formed.
pub trait ConstraintSystem<Scalar: PrimeField>: Sized {
    /// Represents the type of the "root" of this constraint system
    /// so that nested namespaces can minimize indirection.
    type Root: ConstraintSystem<Scalar>;

    /// Return the "one" input variable
    fn one() -> Variable {
        Variable::new_unchecked(Index::Input(0))
    }

    /// Allocate a private variable in the constraint system. The provided function is used to
    /// determine the assignment of the variable. The given `annotation` function is invoked
    /// in testing contexts in order to derive a unique name for this variable in the current
    /// namespace.
    fn alloc<F, A, AR>(&mut self, annotation: A, f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<Scalar, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>;

    /// Allocate a public variable in the constraint system. The provided function is used to
    /// determine the assignment of the variable.
    fn alloc_input<F, A, AR>(&mut self, annotation: A, f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<Scalar, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>;

    /// Enforce that `A` * `B` = `C`. The `annotation` function is invoked in testing contexts
    /// in order to derive a unique name for the constraint in the current namespace.
    fn enforce<A, AR, LA, LB, LC>(&mut self, annotation: A, a: LA, b: LB, c: LC)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
        LA: FnOnce(LinearCombination<Scalar>) -> LinearCombination<Scalar>,
        LB: FnOnce(LinearCombination<Scalar>) -> LinearCombination<Scalar>,
        LC: FnOnce(LinearCombination<Scalar>) -> LinearCombination<Scalar>;

    /// Create a new (sub)namespace and enter into it. Not intended
    /// for downstream use; use `namespace` instead.
    fn push_namespace<NR, N>(&mut self, name_fn: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR;

    /// Exit out of the existing namespace. Not intended for
    /// downstream use; use `namespace` instead.
    fn pop_namespace(&mut self);

    /// Gets the "root" constraint system, bypassing the namespacing.
    /// Not intended for downstream use; use `namespace` instead.
    fn get_root(&mut self) -> &mut Self::Root;

    /// Begin a namespace for this constraint system.
    fn namespace<NR, N>(&mut self, name_fn: N) -> Namespace<'_, Scalar, Self::Root>
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        self.get_root().push_namespace(name_fn);

        Namespace(self.get_root(), PhantomData)
    }
}

/// This is a "namespaced" constraint system which borrows a constraint system (pushing
/// a namespace context) and, when dropped, pops out of the namespace context.
pub struct Namespace<'a, Scalar: PrimeField, CS: ConstraintSystem<Scalar>>(
    &'a mut CS,
    PhantomData<Scalar>,
);

impl<'cs, Scalar: PrimeField, CS: ConstraintSystem<Scalar>> ConstraintSystem<Scalar>
    for Namespace<'cs, Scalar, CS>
{
    type Root = CS::Root;

    fn one() -> Variable {
        CS::one()
    }

    fn alloc<F, A, AR>(&mut self, annotation: A, f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<Scalar, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        self.0.alloc(annotation, f)
    }

    fn alloc_input<F, A, AR>(&mut self, annotation: A, f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<Scalar, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        self.0.alloc_input(annotation, f)
    }

    fn enforce<A, AR, LA, LB, LC>(&mut self, annotation: A, a: LA, b: LB, c: LC)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
        LA: FnOnce(LinearCombination<Scalar>) -> LinearCombination<Scalar>,
        LB: FnOnce(LinearCombination<Scalar>) -> LinearCombination<Scalar>,
        LC: FnOnce(LinearCombination<Scalar>) -> LinearCombination<Scalar>,
    {
        self.0.enforce(annotation, a, b, c)
    }

    // Downstream users who use `namespace` will never interact with these
    // functions and they will never be invoked because the namespace is
    // never a root constraint system.

    fn push_namespace<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        panic!("only the root's push_namespace should be called");
    }

    fn pop_namespace(&mut self) {
        panic!("only the root's pop_namespace should be called");
    }

    fn get_root(&mut self) -> &mut Self::Root {
        self.0.get_root()
    }
}

impl<'a, Scalar: PrimeField, CS: ConstraintSystem<Scalar>> Drop for Namespace<'a, Scalar, CS> {
    fn drop(&mut self) {
        self.get_root().pop_namespace()
    }
}

/// Convenience implementation of ConstraintSystem<Scalar> for mutable references to
/// constraint systems.
impl<'cs, Scalar: PrimeField, CS: ConstraintSystem<Scalar>> ConstraintSystem<Scalar>
    for &'cs mut CS
{
    type Root = CS::Root;

    fn one() -> Variable {
        CS::one()
    }

    fn alloc<F, A, AR>(&mut self, annotation: A, f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<Scalar, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        (**self).alloc(annotation, f)
    }

    fn alloc_input<F, A, AR>(&mut self, annotation: A, f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<Scalar, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        (**self).alloc_input(annotation, f)
    }

    fn enforce<A, AR, LA, LB, LC>(&mut self, annotation: A, a: LA, b: LB, c: LC)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
        LA: FnOnce(LinearCombination<Scalar>) -> LinearCombination<Scalar>,
        LB: FnOnce(LinearCombination<Scalar>) -> LinearCombination<Scalar>,
        LC: FnOnce(LinearCombination<Scalar>) -> LinearCombination<Scalar>,
    {
        (**self).enforce(annotation, a, b, c)
    }

    fn push_namespace<NR, N>(&mut self, name_fn: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        (**self).push_namespace(name_fn)
    }

    fn pop_namespace(&mut self) {
        (**self).pop_namespace()
    }

    fn get_root(&mut self) -> &mut Self::Root {
        (**self).get_root()
    }
}
