extern crate pairing;
extern crate rand;
extern crate bit_vec;
extern crate futures;
extern crate futures_cpupool;
extern crate num_cpus;
extern crate crossbeam;

use pairing::{Engine, Field};
use std::ops::{Add, Sub};
use std::io;

pub mod multicore;
pub mod domain;
pub mod groth16;
pub mod multiexp;

#[derive(Debug)]
pub enum Error {
    PolynomialDegreeTooLarge,
    MalformedVerifyingKey,
    AssignmentMissing,
    UnexpectedIdentity,
    UnconstrainedVariable(Variable),
    IoError(io::Error)
}

impl From<io::Error> for Error {
    fn from(e: io::Error) -> Error {
        Error::IoError(e)
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Variable(Index);

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum Index {
    Input(usize),
    Aux(usize)
}

pub struct LinearCombination<E: Engine>(Vec<(Index, E::Fr)>);

impl<E: Engine> Clone for LinearCombination<E> {
    fn clone(&self) -> LinearCombination<E> {
        LinearCombination(self.0.clone())
    }
}

impl<E: Engine> LinearCombination<E> {
    pub fn zero() -> LinearCombination<E> {
        LinearCombination(vec![])
    }

    pub fn eval(
        &self,
        mut input_density: Option<&mut multiexp::DensityTracker>,
        mut aux_density: Option<&mut multiexp::DensityTracker>,
        input_assignment: &[E::Fr],
        aux_assignment: &[E::Fr]
    ) -> E::Fr
    {
        let mut acc = E::Fr::zero();

        for &(index, coeff) in self.0.iter() {
            let mut tmp;

            match index {
                Index::Input(i) => {
                    tmp = input_assignment[i];
                    if let Some(ref mut v) = input_density {
                        v.inc(i);
                    }
                },
                Index::Aux(i) => {
                    tmp = aux_assignment[i];
                    if let Some(ref mut v) = aux_density {
                        v.inc(i);
                    }
                }
            }

            if coeff == E::Fr::one() {
               acc.add_assign(&tmp);
            } else {
               tmp.mul_assign(&coeff);
               acc.add_assign(&tmp);
            }
        }

        acc
    }
}

impl<E: Engine> Add<Variable> for LinearCombination<E> {
    type Output = LinearCombination<E>;

    fn add(self, other: Variable) -> LinearCombination<E> {
        self + (E::Fr::one(), other)
    }
}

impl<E: Engine> Sub<Variable> for LinearCombination<E> {
    type Output = LinearCombination<E>;

    fn sub(self, other: Variable) -> LinearCombination<E> {
        self - (E::Fr::one(), other)
    }
}

impl<E: Engine> Add<(E::Fr, Variable)> for LinearCombination<E> {
    type Output = LinearCombination<E>;

    fn add(mut self, (coeff, var): (E::Fr, Variable)) -> LinearCombination<E> {
        let mut must_insert = true;

        for &mut (ref index, ref mut fr) in &mut self.0 {
            if *index == var.0 {
                fr.add_assign(&coeff);
                must_insert = false;
                break;
            }
        }

        if must_insert {
            self.0.push((var.0, coeff));
        }

        self
    }
}

impl<E: Engine> Sub<(E::Fr, Variable)> for LinearCombination<E> {
    type Output = LinearCombination<E>;

    fn sub(self, (mut coeff, var): (E::Fr, Variable)) -> LinearCombination<E> {
        coeff.negate();

        self + (coeff, var)
    }
}

impl<'a, E: Engine> Add<&'a LinearCombination<E>> for LinearCombination<E> {
    type Output = LinearCombination<E>;

    fn add(mut self, other: &'a LinearCombination<E>) -> LinearCombination<E> {
        for &(k, v) in other.0.iter() {
            self = self + (v, Variable(k));
        }

        self
    }
}

impl<'a, E: Engine> Sub<&'a LinearCombination<E>> for LinearCombination<E> {
    type Output = LinearCombination<E>;

    fn sub(mut self, other: &'a LinearCombination<E>) -> LinearCombination<E> {
        for &(k, v) in other.0.iter() {
            self = self - (v, Variable(k));
        }

        self
    }
}

pub trait Circuit<E: Engine> {
    type InputMap: Input<E>;

    /// Synthesize the circuit into a rank-1 quadratic constraint system
    #[must_use]
    fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<Self::InputMap, Error>;
}

pub trait Input<E: Engine> {
    /// Synthesize the circuit, except with additional access to public input
    /// variables
    fn synthesize<CS: PublicConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), Error>;
}

pub trait PublicConstraintSystem<E: Engine>: ConstraintSystem<E> {
    /// Allocate a public input that the verifier knows. The provided function is used to
    /// determine the assignment of the variable.
    fn alloc_input<NR, N, F>(
        &mut self,
        name_fn: N,
        f: F
    ) -> Result<Variable, Error>
        where NR: Into<String>, N: FnOnce() -> NR, F: FnOnce() -> Result<E::Fr, Error>;
}

pub trait ConstraintSystem<E: Engine>: Sized {
    type Root: ConstraintSystem<E>;

    /// Return the "one" input variable
    fn one() -> Variable {
        Variable(Index::Input(0))
    }

    /// Allocate a private variable in the constraint system. The provided function is used to
    /// determine the assignment of the variable.
    fn alloc<NR, N, F>(
        &mut self,
        name_fn: N,
        f: F
    ) -> Result<Variable, Error>
        where NR: Into<String>, N: FnOnce() -> NR, F: FnOnce() -> Result<E::Fr, Error>;

    /// Enforce that `A` * `B` = `C`.
    fn enforce<NR: Into<String>, N: FnOnce() -> NR>(
        &mut self,
        name_fn: N,
        a: LinearCombination<E>,
        b: LinearCombination<E>,
        c: LinearCombination<E>
    );

    fn push_namespace<NR, N>(&mut self, _: N)
        where NR: Into<String>, N: FnOnce() -> NR
    {
        // Default is to do nothing.
    }

    fn pop_namespace(&mut self)
    {
        // Default is to do nothing.
    }

    /// Begin a namespace for the constraint system
    fn namespace<'a, NR, N>(
        &'a mut self,
        name_fn: N
    ) -> Namespace<'a, E, Self::Root>
        where NR: Into<String>, N: FnOnce() -> NR;
}

impl<'cs, E: Engine, CS: ConstraintSystem<E>> ConstraintSystem<E> for &'cs mut CS {
    type Root = CS::Root;

    /// Allocate a private variable in the constraint system. The provided function is used to
    /// determine the assignment of the variable.
    fn alloc<NR, N, F>(
        &mut self,
        name_fn: N,
        f: F
    ) -> Result<Variable, Error>
        where NR: Into<String>, N: FnOnce() -> NR, F: FnOnce() -> Result<E::Fr, Error>
    {
        (*self).alloc(name_fn, f)
    }

    /// Enforce that `A` * `B` = `C`.
    fn enforce<NR: Into<String>, N: FnOnce() -> NR>(
        &mut self,
        name_fn: N,
        a: LinearCombination<E>,
        b: LinearCombination<E>,
        c: LinearCombination<E>
    )
    {
        (*self).enforce(name_fn, a, b, c)
    }

    fn push_namespace<NR, N>(&mut self, name_fn: N)
        where NR: Into<String>, N: FnOnce() -> NR
    {
        (*self).push_namespace(name_fn)
    }

    fn pop_namespace(&mut self)
    {
        (*self).pop_namespace()
    }

    /// Begin a namespace for the constraint system
    fn namespace<'a, NR, N>(
        &'a mut self,
        name_fn: N
    ) -> Namespace<'a, E, Self::Root>
        where NR: Into<String>, N: FnOnce() -> NR
    {
        (*self).namespace(name_fn)
    }
}

use std::marker::PhantomData;

pub struct Namespace<'a, E: Engine, CS: ConstraintSystem<E> + 'a>(&'a mut CS, PhantomData<E>);

impl<'cs, E: Engine, CS: ConstraintSystem<E>> ConstraintSystem<E> for Namespace<'cs, E, CS> {
    type Root = CS;

    fn alloc<NR, N, F>(
        &mut self,
        name_fn: N,
        f: F
    ) -> Result<Variable, Error>
        where NR: Into<String>, N: FnOnce() -> NR, F: FnOnce() -> Result<E::Fr, Error>
    {
        self.0.alloc(name_fn, f)
    }

    fn enforce<NR: Into<String>, N: FnOnce() -> NR>(
        &mut self,
        name_fn: N,
        a: LinearCombination<E>,
        b: LinearCombination<E>,
        c: LinearCombination<E>
    )
    {
        self.0.enforce(name_fn, a, b, c)
    }

    fn push_namespace<NR, N>(&mut self, name_fn: N)
        where NR: Into<String>, N: FnOnce() -> NR
    {
        self.0.push_namespace(name_fn);
    }

    fn pop_namespace(&mut self)
    {
        self.0.pop_namespace();
    }

    /// Begin a namespace for the constraint system
    fn namespace<'a, NR, N>(
        &'a mut self,
        name_fn: N
    ) -> Namespace<'a, E, Self::Root>
        where NR: Into<String>, N: FnOnce() -> NR
    {
        self.0.push_namespace(name_fn);

        Namespace(self.0, PhantomData)
    }
}

impl<'a, E: Engine, CS: ConstraintSystem<E>> Drop for Namespace<'a, E, CS> {
    fn drop(&mut self) {
        self.0.pop_namespace()
    }
}

use std::collections::HashMap;

#[derive(Debug)]
enum NamedObject {
    Constraint(usize),
    Input(usize),
    Aux(usize),
    Namespace
}

/// Constraint system for testing purposes.
pub struct TestConstraintSystem<E: Engine> {
    named_objects: HashMap<String, NamedObject>,
    current_namespace: Vec<String>,
    constraints: Vec<(LinearCombination<E>, LinearCombination<E>, LinearCombination<E>, String)>,
    inputs: Vec<E::Fr>,
    aux: Vec<E::Fr>
}

impl<E: Engine> TestConstraintSystem<E> {
    pub fn new() -> TestConstraintSystem<E> {
        TestConstraintSystem {
            named_objects: HashMap::new(),
            current_namespace: vec![],
            constraints: vec![],
            inputs: vec![E::Fr::one()],
            aux: vec![]
        }
    }

    pub fn which_is_unsatisfied(&self) -> Option<&str> {
        for &(ref a, ref b, ref c, ref path) in &self.constraints {
            let mut a = a.eval(None, None, &self.inputs, &self.aux);
            let b = b.eval(None, None, &self.inputs, &self.aux);
            let c = c.eval(None, None, &self.inputs, &self.aux);

            a.mul_assign(&b);

            if a != c {
                return Some(&*path)
            }
        }

        None
    }

    pub fn is_satisfied(&self) -> bool
    {
        self.which_is_unsatisfied().is_none()
    }

    pub fn num_constraints(&self) -> usize
    {
        self.constraints.len()
    }

    pub fn assign(&mut self, path: &str, to: E::Fr)
    {
        match self.named_objects.get(path) {
            Some(&NamedObject::Input(index)) => self.inputs[index] = to,
            Some(&NamedObject::Aux(index)) => self.aux[index] = to,
            Some(e) => panic!("tried to assign `{:?}` a value at path: {}", e, path),
            _ => panic!("no variable exists at path: {}", path)
        }
    }

    pub fn get(&mut self, path: &str) -> E::Fr
    {
        match self.named_objects.get(path) {
            Some(&NamedObject::Input(index)) => self.inputs[index],
            Some(&NamedObject::Aux(index)) => self.aux[index],
            Some(e) => panic!("tried to get value of `{:?}` at path: {}", e, path),
            _ => panic!("no variable exists at path: {}", path)
        }
    }

    fn set_named_obj(&mut self, path: String, to: NamedObject) {
        if self.named_objects.contains_key(&path) {
            panic!("tried to create object at existing path: {}", path);
        }

        self.named_objects.insert(path, to);
    }
}

fn compute_path(ns: &[String], this: String) -> String {
    if this.chars().any(|a| a == '/') {
        panic!("'/' is not allowed in names");
    }

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

impl<E: Engine> PublicConstraintSystem<E> for TestConstraintSystem<E> {
    fn alloc_input<NR, N, F>(
        &mut self,
        name_fn: N,
        f: F
    ) -> Result<Variable, Error>
        where NR: Into<String>, N: FnOnce() -> NR, F: FnOnce() -> Result<E::Fr, Error>
    {
        let this_path = compute_path(&self.current_namespace, name_fn().into());
        let this_obj = NamedObject::Input(self.inputs.len());
        self.set_named_obj(this_path, this_obj);

        let var = Variable(Index::Input(self.inputs.len()));

        self.inputs.push(f()?);

        Ok(var)
    }
}

impl<E: Engine> ConstraintSystem<E> for TestConstraintSystem<E> {
    type Root = Self;

    fn alloc<NR, N, F>(
        &mut self,
        name_fn: N,
        f: F
    ) -> Result<Variable, Error>
        where NR: Into<String>, N: FnOnce() -> NR, F: FnOnce() -> Result<E::Fr, Error>
    {
        let this_path = compute_path(&self.current_namespace, name_fn().into());
        let this_obj = NamedObject::Aux(self.aux.len());
        self.set_named_obj(this_path, this_obj);

        let var = Variable(Index::Aux(self.aux.len()));

        self.aux.push(f()?);

        Ok(var)
    }

    fn enforce<NR: Into<String>, N: FnOnce() -> NR>(
        &mut self,
        name_fn: N,
        a: LinearCombination<E>,
        b: LinearCombination<E>,
        c: LinearCombination<E>
    )
    {
        let this_path = compute_path(&self.current_namespace, name_fn().into());
        let this_obj = NamedObject::Constraint(self.constraints.len());
        self.set_named_obj(this_path.clone(), this_obj);

        self.constraints.push((a, b, c, this_path));
    }

    fn push_namespace<NR, N>(&mut self, name_fn: N)
        where NR: Into<String>, N: FnOnce() -> NR
    {
        let name = name_fn().into();
        let this_path = compute_path(&self.current_namespace, name.clone());

        self.set_named_obj(this_path, NamedObject::Namespace);

        self.current_namespace.push(name);
    }

    fn pop_namespace(&mut self)
    {
        self.current_namespace.pop();
    }

    /// Begin a namespace for the constraint system
    fn namespace<'a, NR, N>(
        &'a mut self,
        name_fn: N
    ) -> Namespace<'a, E, Self::Root>
        where NR: Into<String>, N: FnOnce() -> NR
    {
        self.push_namespace(name_fn);

        Namespace(self, PhantomData)
    }
}
