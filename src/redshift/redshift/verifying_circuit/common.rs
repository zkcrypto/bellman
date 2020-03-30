use crate::pairing::{Engine};
use crate::pairing::ff::{Field};
use crate::{SynthesisError};
use crate::cs::*;
use crate::redshift::IOP::hashes::rescue::*;

use std::ops::{Add, Sub};
use std::marker::PhantomData;

// TODO: put Coeff at top level module! (not in gates)
// and use Coeff as value of constant and allocated num

pub struct Params<E: Engine> {
    pub rescue_params: RescueParams<E::Fr>,
}

impl<E: Engine> Params<E> {
    pub fn alpha(&self) -> u64 {
        self.rescue_params.RESCUE_ALPHA
    }

    pub fn inalpha(&self) -> &[u64] {
        &self.rescue_params.RESCUE_INVALPHA
    }
}


#[derive(Clone, Debug)]
pub struct AllocatedNum<E: Engine> {
    value: Option<E::Fr>,
    var: Variable,
}

impl<E: Engine> Copy for AllocatedNum<E> {}

#[derive(Clone, Debug)]
pub enum Num<E: Engine> {
    Constant(E::Fr),
    Allocated(E::Fr, AllocatedNum<E>),
}

impl<E: Engine> Copy for Num<E> {}


impl<E: Engine> From<AllocatedNum<E>> for Num<E> {
    fn from(num: AllocatedNum<E>) -> Self {
        Num::Allocated(E::Fr::one(), num)
    }
}

#[derive(Clone, Debug)]
pub struct Combination<E: Engine> {
    value: Option<E::Fr>,
    terms: Vec<Num<E>>,
}

impl<E: Engine> From<AllocatedNum<E>> for Combination<E> {
    fn from(num: AllocatedNum<E>) -> Self {
        Combination {
            value: num.value,
            terms: vec![num.into()],
        }
    }
}

impl<E: Engine> From<Num<E>> for Combination<E> {
    fn from(num: Num<E>) -> Self {
        Combination {
            value: num.value(),
            terms: vec![num],
        }
    }
}

fn double<F: Field>(x: Option<F>) -> Option<F>
{
    let res = match x {
        None => None,
        Some(mut x) => {
            x.double();
            Some(x)
        }
    };
    res
}

fn mul<F: Field>(x: Option<F>, y: Option<F>) -> Option<F> {
    let res = match (x, y) {
        (Some(mut x), Some(y)) => { 
            x.mul_assign(&y);
            Some(x)
        }
        (_, _) => None,
    };
    res
}

fn add<F: Field>(x: Option<F>, y: Option<F>) -> Option<F> {
    let res = match (x, y) {
        (Some(mut x), Some(y)) => { 
            x.add_assign(&y);
            Some(x)
        }
        (_, _) => None,
    };
    res
}

pub fn enforce_zero<E: Engine, CS: ConstraintSystem<E>>(cs: &mut CS, a: &LinearCombination<E>) {
    cs.enforce(|| { "enforce zero"}, |lc| {lc + a}, |lc| {lc + CS::one()}, |lc| { lc });
}


fn constrain_pow_five<E, CS>(
    cs: &mut CS,
    base: &LinearCombination<E>,
    res: &LinearCombination<E>,
    x: Option<E::Fr>,
) -> Result<(), SynthesisError>
where
    E: Engine,
    CS: ConstraintSystem<E>,
{
    let x2 = double(x);
    let x4 = double(x2);

    let var2 = cs.alloc(|| "x^2", || {
        x2.ok_or(SynthesisError::AssignmentMissing)
    })?;

    cs.enforce(
        || "x * x",
        |lc| lc + base,
        |lc| lc + base,
        |lc| lc + var2
    );

    let var4 = cs.alloc(|| "x^4", || {
        x4.ok_or(SynthesisError::AssignmentMissing)
    })?;

    cs.enforce(
        || "x^2 * x^2",
        |lc| lc + var2,
        |lc| lc + var2,
        |lc| lc + var4
    );

    cs.enforce(
        || "x * x^4",
        |lc| lc + var4,
        |lc| lc + base,
        |lc| lc + res,
    );

    Ok(())  
}


impl<E: Engine> AllocatedNum<E> {
    
    pub fn alloc<CS, FF>(cs: &mut CS, value: FF) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
        FF: FnOnce() -> Result<E::Fr, SynthesisError>,
    {
        let mut new_value = None;
        let var = cs.alloc(|| "num", || {
            let tmp = value()?;

            new_value = Some(tmp);

            Ok(tmp)
        })?;

        Ok(AllocatedNum {
            value: new_value,
            var: var
        })
    }

    pub fn alloc_input<CS, FF>(cs: &mut CS, value: FF) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
        FF: FnOnce() -> Result<E::Fr, SynthesisError>,
    {
        let mut new_value = None;
        let var = cs.alloc_input(|| "num", || {
            let tmp = value()?;

            new_value = Some(tmp);

            Ok(tmp)
        })?;

        Ok(AllocatedNum {
            value: new_value,
            var: var
        })
    }

    pub fn get_value(&self) -> Option<E::Fr> {
        self.value
    }

    pub fn get_variable(&self) -> Variable {
        self.var
    }
}


impl<E: Engine> Num<E> {
    pub fn scale(&self, val: E::Fr) -> Self {
        match self {
            Num::Constant(ref coeff) => {
                let mut temp = coeff.clone();
                temp.mul_assign(&val);
                Num::Constant(temp)
            },
            Num::Allocated(ref coeff, ref var) => {
                let mut temp = coeff.clone();
                temp.mul_assign(&val);
                Num::Allocated(temp, var.clone())
            }
        }
    }

    pub fn constant(val: E::Fr) -> Self {
        Num::Constant(val)
    }

    pub fn zero() -> Self {
        Num::constant(E::Fr::zero())
    }

    pub fn one() -> Self {
        Num::constant(E::Fr::one())
    }

    pub fn is_constant(&self) -> bool {
        match *self {
            Num::Constant(_) => true,
            _ => false,
        }
    }

    pub fn value(&self) -> Option<E::Fr> {
        match self {
            Num::Constant(v) => Some(*v),
            Num::Allocated(coeff, var) => var.value.map(|v| {
                let mut temp = *coeff;
                temp.mul_assign(&v);
                temp
            }),
        }
    }

    pub fn lc<CS: ConstraintSystem<E>>(&self, _cs: &mut CS) -> LinearCombination<E> {
        LinearCombination::zero()
            + match self {
                Num::Constant(v) => (*v, CS::one()),
                Num::Allocated(coeff, num) => (*coeff, num.var),
            }
    }
}


impl<E: Engine> Combination<E> {
    pub fn zero() -> Self {
        Combination {
            value: Some(E::Fr::zero()),
            terms: vec![],
        }
    }

    pub fn scale(self, by: E::Fr) -> Self {
        let value = self.value.map(|v| {
            let mut temp = v.clone();
            temp.mul_assign(&by);
            temp
        });
        let terms = self.terms.into_iter().map(|t| t.scale(by)).collect();

        Combination { value, terms }
    }

    pub fn get_value(&self) -> Option<E::Fr> {
        self.value
    }

    pub fn lc<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> LinearCombination<E> {
        let mut acc = LinearCombination::zero();

        for term in &self.terms {
            acc = acc + &term.lc(cs);
        }

        acc
    }
    
    pub fn rescue_alpha<CS>(&self, cs: &mut CS, params: &Params<E>) -> Result<Num<E>, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let any_allocated = self.terms.iter().any(|n| !n.is_constant());

        if any_allocated {

            assert_eq!(params.alpha(), 5);
            
            let base_value = self.get_value();
            let base_lc = self.lc(cs);

            let result_value = base_value.and_then(|num| Some(num.pow(&[params.alpha()])));
            let result_alloced_var = AllocatedNum::alloc(cs, || result_value.ok_or(SynthesisError::AssignmentMissing))?;
            let result_var : Num<E> = result_alloced_var.into();
            let result_lc = result_var.lc(cs);
            constrain_pow_five(cs, &base_lc, &result_lc, base_value)?;

            Ok(result_var)
        } else {
            // We can just return a constant
            let base_value = self.value.ok_or(SynthesisError::AssignmentMissing)?;
            Ok(Num::constant(base_value.pow(&[params.alpha(), 0, 0, 0])))
        }
    }

    pub fn rescue_invalpha<CS>(&self, cs: &mut CS, params: &Params<E>) -> Result<Num<E>, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let any_allocated = self.terms.iter().any(|n| !n.is_constant());

        if any_allocated {

            assert_eq!(params.alpha(), 5);

            let result_value = self.get_value();
            let result_lc = self.lc(cs);

            let base_value = result_value.and_then(|num| Some(num.pow(params.inalpha())));
            let base_allocated_var = AllocatedNum::alloc(cs, || base_value.ok_or(SynthesisError::AssignmentMissing))?;
            let base_var : Num<E> = base_allocated_var.into();
            let base_lc = base_var.lc(cs);
            constrain_pow_five(cs, &base_lc, &result_lc, base_value)?;

            Ok(base_var)
        } else {
            // We can just return a constant
            let base_value = self.value.ok_or(SynthesisError::AssignmentMissing)?;
            Ok(Num::constant(base_value.pow(params.inalpha())))
        }
    }

    pub fn add_assign_num(&mut self, other: &Num<E>) {
        self.value = add(self.value, other.value());
        self.terms.push(other.clone());
    }

    // check is the combination in question exactly contains the only one element (or even empty)
    // it yes - returns that unique element
    pub fn simplify<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<Num<E>, SynthesisError> {
        let any_allocated = self.terms.iter().any(|n| !n.is_constant());
        let res = if any_allocated {
            let res = match self.terms.len() {
                0 => Num::zero(),
                1 => self.terms[0].clone(),
                _ => {
                    let out_alloc = AllocatedNum::alloc(&mut cs.namespace(|| "simplified element"), || {
                        self.get_value().ok_or(SynthesisError::AssignmentMissing)
                    })?;
                    let out : Num<E> = out_alloc.into();

                    let in_lc = self.lc(cs);
                    let lc = out.lc(cs) - &in_lc;
                    enforce_zero(cs, &lc);

                    // As we've constrained this currentcombination, we can
                    // substitute for the new variable to shorten subsequent combinations.
                    *self = out.clone().into();
                    out
                }
            };
            res
        }
        else {
            // We can just return a constant
            let base_value = self.value.ok_or(SynthesisError::AssignmentMissing)?;
            let new_num = Num::constant(base_value);
            *self = new_num.clone().into();
            new_num
        };
        Ok(res)
    }
}









    
