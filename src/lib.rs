extern crate pairing;

use pairing::{Engine, Field};
use std::ops::{Add, Sub};
use std::fmt;
use std::error::Error;

/// This represents a linear combination of some variables, with coefficients
/// in the scalar field of a pairing-friendly elliptic curve group.
pub struct LinearCombination<T, E: Engine>(Vec<(T, E::Fr)>);

impl<T, E: Engine> AsRef<[(T, E::Fr)]> for LinearCombination<T, E> {
    fn as_ref(&self) -> &[(T, E::Fr)] {
        &self.0
    }
}

impl<T, E: Engine> LinearCombination<T, E> {
    pub fn zero() -> LinearCombination<T, E> {
        LinearCombination(vec![])
    }
}

impl<T, E: Engine> Add<(E::Fr, T)> for LinearCombination<T, E> {
    type Output = LinearCombination<T, E>;

    fn add(mut self, (coeff, var): (E::Fr, T)) -> LinearCombination<T, E> {
        self.0.push((var, coeff));

        self
    }
}

impl<T, E: Engine> Sub<(E::Fr, T)> for LinearCombination<T, E> {
    type Output = LinearCombination<T, E>;

    fn sub(self, (mut coeff, var): (E::Fr, T)) -> LinearCombination<T, E> {
        coeff.negate();

        self + (coeff, var)
    }
}

impl<T, E: Engine> Add<T> for LinearCombination<T, E> {
    type Output = LinearCombination<T, E>;

    fn add(self, other: T) -> LinearCombination<T, E> {
        self + (E::Fr::one(), other)
    }
}

impl<T, E: Engine> Sub<T> for LinearCombination<T, E> {
    type Output = LinearCombination<T, E>;

    fn sub(self, other: T) -> LinearCombination<T, E> {
        self - (E::Fr::one(), other)
    }
}

#[test]
fn test_lc() {
    use pairing::bls12_381::{Bls12, Fr};

    let a = LinearCombination::<usize, Bls12>::zero() + 0usize + 1usize + 2usize - 3usize;

    let mut negone = Fr::one();
    negone.negate();

    assert_eq!(a.0, vec![(0usize, Fr::one()), (1usize, Fr::one()), (2usize, Fr::one()), (3usize, negone)]);
}

/// This is an error that could occur during circuit synthesis contexts,
/// such as CRS generation, proving or verification.
#[derive(Debug)]
pub enum SynthesisError {
    AssignmentMissing
}

impl Error for SynthesisError {
    fn description(&self) -> &str {
        match *self {
            SynthesisError::AssignmentMissing => "an assignment for a variable could not be computed"
        }
    }
}

impl fmt::Display for SynthesisError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self.description())
    }
}

pub trait ConstraintSystem<E: Engine>: Sized {
    type Variable: Sized + Copy + Clone;

    /// Represents the type of the "root" of this constraint system
    /// so that nested namespaces can minimize indirection.
    type Root: ConstraintSystem<E, Variable=Self::Variable>;

    /// Return the "one" input variable
    fn one(&self) -> Self::Variable;

    /// Allocate a private variable in the constraint system. The provided function is used to
    /// determine the assignment of the variable. The given `annotation` function is invoked
    /// in testing contexts in order to derive a unique name for this variable in the current
    /// namespace.
    fn alloc<F, A, AR>(
        &mut self,
        annotation: A,
        f: F
    ) -> Result<Self::Variable, SynthesisError>
        where F: FnOnce() -> Result<E::Fr, SynthesisError>, A: FnOnce() -> AR, AR: Into<String>;

    /// Enforce that `A` * `B` = `C`. The `annotation` function is invoked in testing contexts
    /// in order to derive a unique name for the constraint in the current namespace.
    fn enforce<A, AR>(
        &mut self,
        annotation: A,
        a: LinearCombination<Self::Variable, E>,
        b: LinearCombination<Self::Variable, E>,
        c: LinearCombination<Self::Variable, E>
    )
        where A: FnOnce() -> AR, AR: Into<String>;

    /// Create a new (sub)namespace and enter into it. Not intended
    /// for downstream use; use `namespace` instead.
    fn push_namespace<NR, N>(&mut self, name_fn: N)
        where NR: Into<String>, N: FnOnce() -> NR;

    /// Exit out of the existing namespace. Not intended for
    /// downstream use; use `namespace` instead.
    fn pop_namespace(&mut self);

    /// Gets the "root" constraint system, bypassing the namespacing.
    /// Not intended for downstream use; use `namespace` instead.
    fn get_root(&mut self) -> &mut Self::Root;

    /// Begin a namespace for this constraint system.
    fn namespace<'a, NR, N>(
        &'a mut self,
        name_fn: N
    ) -> Namespace<'a, E, Self::Root>
        where NR: Into<String>, N: FnOnce() -> NR
    {
        self.get_root().push_namespace(name_fn);

        Namespace(self.get_root(), PhantomData)
    }
}

pub trait PublicConstraintSystem<E: Engine>: ConstraintSystem<E>
{
    /// Represents the type of the "root" of this constraint system
    /// so that nested namespaces can minimize indirection.
    type PublicRoot: PublicConstraintSystem<E, Variable=Self::Variable>;

    /// Allocate a public variable in the constraint system. The provided function is used to
    /// determine the assignment of the variable.
    fn alloc_input<F, A, AR>(
        &mut self,
        annotation: A,
        f: F
    ) -> Result<Self::Variable, SynthesisError>
        where F: FnOnce() -> Result<E::Fr, SynthesisError>, A: FnOnce() -> AR, AR: Into<String>;

    /// Gets the "root" constraint system, bypassing the namespacing.
    /// Not intended for downstream use; use `namespace` instead.
    fn get_public_root(&mut self) -> &mut Self::PublicRoot;

    /// Begin a namespace for this constraint system.
    fn namespace_public<'a, NR, N>(
        &'a mut self,
        name_fn: N
    ) -> Namespace<'a, E, Self::PublicRoot>
        where NR: Into<String>, N: FnOnce() -> NR
    {
        self.get_root().push_namespace(name_fn);

        Namespace(self.get_public_root(), PhantomData)
    }
}

use std::marker::PhantomData;

/// This is a "namespaced" constraint system which borrows a constraint system (pushing
/// a namespace context) and, when dropped, pops out of the namespace context.
pub struct Namespace<'a, E: Engine, CS: ConstraintSystem<E> + 'a>(&'a mut CS, PhantomData<E>);

impl<'cs, E: Engine, CS: PublicConstraintSystem<E>> PublicConstraintSystem<E> for Namespace<'cs, E, CS> {
    type PublicRoot = CS::PublicRoot;

    fn alloc_input<F, A, AR>(
        &mut self,
        annotation: A,
        f: F
    ) -> Result<Self::Variable, SynthesisError>
        where F: FnOnce() -> Result<E::Fr, SynthesisError>, A: FnOnce() -> AR, AR: Into<String>
    {
        self.0.alloc_input(annotation, f)
    }

    fn get_public_root(&mut self) -> &mut Self::PublicRoot
    {
        self.0.get_public_root()
    }
}

impl<'cs, E: Engine, CS: ConstraintSystem<E>> ConstraintSystem<E> for Namespace<'cs, E, CS> {
    type Variable = CS::Variable;
    type Root = CS::Root;

    fn one(&self) -> Self::Variable {
        self.0.one()
    }

    fn alloc<F, A, AR>(
        &mut self,
        annotation: A,
        f: F
    ) -> Result<Self::Variable, SynthesisError>
        where F: FnOnce() -> Result<E::Fr, SynthesisError>, A: FnOnce() -> AR, AR: Into<String>
    {
        self.0.alloc(annotation, f)
    }

    fn enforce<A, AR>(
        &mut self,
        annotation: A,
        a: LinearCombination<Self::Variable, E>,
        b: LinearCombination<Self::Variable, E>,
        c: LinearCombination<Self::Variable, E>
    )
        where A: FnOnce() -> AR, AR: Into<String>
    {
        self.0.enforce(annotation, a, b, c)
    }

    // Downstream users who use `namespace` will never interact with these
    // functions and they will never be invoked because the namespace is
    // never a root constraint system.

    fn push_namespace<NR, N>(&mut self, _: N)
        where NR: Into<String>, N: FnOnce() -> NR
    {
        panic!("only the root's push_namespace should be called");
    }

    fn pop_namespace(&mut self)
    {
        panic!("only the root's pop_namespace should be called");
    }

    fn get_root(&mut self) -> &mut Self::Root
    {
        self.0.get_root()
    }
}

impl<'a, E: Engine, CS: ConstraintSystem<E>> Drop for Namespace<'a, E, CS> {
    fn drop(&mut self) {
        self.get_root().pop_namespace()
    }
}

/// Convenience implementation of PublicConstraintSystem<E> for mutable references to
/// public constraint systems.
impl<'cs, E: Engine, CS: PublicConstraintSystem<E>> PublicConstraintSystem<E> for &'cs mut CS {
    type PublicRoot = CS::PublicRoot;

    fn alloc_input<F, A, AR>(
        &mut self,
        annotation: A,
        f: F
    ) -> Result<Self::Variable, SynthesisError>
        where F: FnOnce() -> Result<E::Fr, SynthesisError>, A: FnOnce() -> AR, AR: Into<String>
    {
        (**self).alloc_input(annotation, f)
    }

    fn get_public_root(&mut self) -> &mut Self::PublicRoot
    {
        (**self).get_public_root()
    }
}

/// Convenience implementation of ConstraintSystem<E> for mutable references to
/// constraint systems.
impl<'cs, E: Engine, CS: ConstraintSystem<E>> ConstraintSystem<E> for &'cs mut CS {
    type Variable = CS::Variable;
    type Root = CS::Root;

    fn one(&self) -> Self::Variable {
        (**self).one()
    }

    fn alloc<F, A, AR>(
        &mut self,
        annotation: A,
        f: F
    ) -> Result<Self::Variable, SynthesisError>
        where F: FnOnce() -> Result<E::Fr, SynthesisError>, A: FnOnce() -> AR, AR: Into<String>
    {
        (**self).alloc(annotation, f)
    }

    fn enforce<A, AR>(
        &mut self,
        annotation: A,
        a: LinearCombination<Self::Variable, E>,
        b: LinearCombination<Self::Variable, E>,
        c: LinearCombination<Self::Variable, E>
    )
        where A: FnOnce() -> AR, AR: Into<String>
    {
        (**self).enforce(annotation, a, b, c)
    }

    fn push_namespace<NR, N>(&mut self, name_fn: N)
        where NR: Into<String>, N: FnOnce() -> NR
    {
        (**self).push_namespace(name_fn)
    }

    fn pop_namespace(&mut self)
    {
        (**self).pop_namespace()
    }

    fn get_root(&mut self) -> &mut Self::Root
    {
        (**self).get_root()
    }
}

#[test]
fn test_cs() {
    use pairing::bls12_381::{Bls12, Fr};

    #[derive(PartialEq, Copy, Clone)]
    enum Var {
        Input(usize),
        Aux(usize)
    }

    struct MySillyConstraintSystem<E: Engine> {
        inputs: Vec<(E::Fr, String)>,
        aux: Vec<(E::Fr, String)>,
        constraints: Vec<(LinearCombination<Var, E>, LinearCombination<Var, E>, LinearCombination<Var, E>, String)>,
        current_namespace: Vec<String>
    }

    fn compute_path(ns: &[String], this: String) -> String {
        let mut name = String::new();

        let mut needs_separation = false;
        for ns in ns.iter().chain(Some(&this).into_iter())
        {
            if needs_separation {
                name += "/";
            }

            name += ns;
            needs_separation = true;
        }

        name
    }

    impl<E: Engine> PublicConstraintSystem<E> for MySillyConstraintSystem<E> {
        type PublicRoot = Self;

        fn alloc_input<F, A, AR>(
            &mut self,
            annotation: A,
            f: F
        ) -> Result<Self::Variable, SynthesisError>
            where F: FnOnce() -> Result<E::Fr, SynthesisError>, A: FnOnce() -> AR, AR: Into<String>
        {
            let index = self.inputs.len();
            let path = compute_path(&self.current_namespace, annotation().into());
            self.inputs.push((f()?, path));

            Ok(Var::Input(index))
        }

        fn get_public_root(&mut self) -> &mut Self::PublicRoot
        {
            self
        }
    }

    impl<E: Engine> ConstraintSystem<E> for MySillyConstraintSystem<E> {
        type Variable = Var;
        type Root = Self;

        fn one(&self) -> Self::Variable {
            Var::Input(0)
        }

        fn alloc<F, A, AR>(
            &mut self,
            annotation: A,
            f: F
        ) -> Result<Self::Variable, SynthesisError>
            where F: FnOnce() -> Result<E::Fr, SynthesisError>, A: FnOnce() -> AR, AR: Into<String>
        {
            let index = self.aux.len();
            let path = compute_path(&self.current_namespace, annotation().into());
            self.aux.push((f()?, path));

            Ok(Var::Aux(index))
        }

        fn enforce<A, AR>(
            &mut self,
            annotation: A,
            a: LinearCombination<Self::Variable, E>,
            b: LinearCombination<Self::Variable, E>,
            c: LinearCombination<Self::Variable, E>
        )
            where A: FnOnce() -> AR, AR: Into<String>
        {
            let path = compute_path(&self.current_namespace, annotation().into());

            self.constraints.push((a, b, c, path));
        }

        fn push_namespace<NR, N>(&mut self, name_fn: N)
        where NR: Into<String>, N: FnOnce() -> NR
        {
            self.current_namespace.push(name_fn().into());
        }

        fn pop_namespace(&mut self)
        {
            self.current_namespace.pop();
        }

        fn get_root(&mut self) -> &mut Self::Root
        {
            self
        }
    }

    fn do_stuff_with_pcs<E: Engine, CS: PublicConstraintSystem<E>>(mut cs: CS, one_more: bool)
    {
        cs.alloc_input(|| "something", || Ok(E::Fr::zero())).unwrap();

        if one_more {
            do_stuff_with_pcs(cs.namespace_public(|| "cool namespace"), false);
        }
    }

    let mut cs = MySillyConstraintSystem::<Bls12> {
        inputs: vec![(Fr::one(), "ONE".into())],
        aux: vec![],
        constraints: vec![],
        current_namespace: vec![]
    };
    cs.alloc(|| "something", || Ok(Fr::zero())).unwrap();
    assert_eq!(cs.inputs, vec![(Fr::one(), "ONE".into())]);
    assert_eq!(cs.aux, vec![(Fr::zero(), "something".into())]);
    {
        let mut cs = cs.namespace(|| "woohoo");

        cs.alloc(|| "whatever", || Ok(Fr::one())).unwrap();
        cs.alloc(|| "you", || Ok(Fr::zero())).unwrap();
        cs.alloc(|| "say", || Ok(Fr::one())).unwrap();

        {
            let mut cs = cs.namespace(|| "hehe");

            let v1 = cs.alloc(|| "hehe, indeed", || Ok(Fr::one())).unwrap();
            let v2 = cs.alloc_input(|| "works lol", || Ok(Fr::zero())).unwrap();

            let one = cs.one();

            cs.enforce(
                || "great constraint",
                LinearCombination::zero() + v1,
                LinearCombination::zero() + one,
                LinearCombination::zero() + v2
            );
        }
    }
    assert_eq!(cs.aux, vec![
        (Fr::zero(), "something".into()),
        (Fr::one(), "woohoo/whatever".into()),
        (Fr::zero(), "woohoo/you".into()),
        (Fr::one(), "woohoo/say".into()),
        (Fr::one(), "woohoo/hehe/hehe, indeed".into()),
    ]);
    assert_eq!(cs.inputs, vec![
        (Fr::one(), "ONE".into()),
        (Fr::zero(), "woohoo/hehe/works lol".into()),
    ]);
    assert!(cs.constraints.len() == 1);
    assert!((cs.constraints[0].0).0 == vec![(Var::Aux(4), Fr::one())]);
    assert!((cs.constraints[0].1).0 == vec![(Var::Input(0), Fr::one())]);
    assert!((cs.constraints[0].2).0 == vec![(Var::Input(1), Fr::one())]);
    assert!(cs.constraints[0].3 == "woohoo/hehe/great constraint");

    do_stuff_with_pcs(cs.namespace(|| "namey"), true);

    assert_eq!(cs.inputs, vec![
        (Fr::one(), "ONE".into()),
        (Fr::zero(), "woohoo/hehe/works lol".into()),
        (Fr::zero(), "namey/something".into()),
        (Fr::zero(), "namey/cool namespace/something".into()),
    ]);
}
