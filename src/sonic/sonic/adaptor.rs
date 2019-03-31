use crate::pairing::ff::{Field, PrimeField};
use crate::pairing::{Engine, CurveProjective};

// this one is for all external interfaces
// use crate::{LinearCombination, ConstraintSystem, Circuit, Variable};

use crate::SynthesisError;

use crate::sonic::srs::SRS;
use crate::sonic::cs::LinearCombination as SonicLinearCombination;
use crate::sonic::cs::Circuit as SonicCircuit;
use crate::sonic::cs::ConstraintSystem as SonicConstraintSystem;
use crate::sonic::cs::Variable as SonicVariable;
use crate::sonic::cs::Coeff;
use std::marker::PhantomData;

pub struct Adaptor<'a, E: Engine, CS: SonicConstraintSystem<E> + 'a> {
    cs: &'a mut CS,
    _marker: PhantomData<E>,
}

impl<'a, E: Engine, CS: SonicConstraintSystem<E> + 'a> crate::ConstraintSystem<E>
    for Adaptor<'a, E, CS>
{
    type Root = Self;

    // this is an important change
    fn one() -> crate::Variable {
        crate::Variable::new_unchecked(crate::Index::Input(1))
    }

    fn alloc<F, A, AR>(&mut self, _: A, f: F) -> Result<crate::Variable, crate::SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, crate::SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        let var = self.cs.alloc(|| {
            f().map_err(|_| crate::SynthesisError::AssignmentMissing)
        }).map_err(|_| crate::SynthesisError::AssignmentMissing)?;

        Ok(match var {
            SonicVariable::A(index) => crate::Variable::new_unchecked(crate::Index::Input(index)),
            SonicVariable::B(index) => crate::Variable::new_unchecked(crate::Index::Aux(index)),
            _ => unreachable!(),
        })
    }

    fn alloc_input<F, A, AR>(
        &mut self,
        _: A,
        f: F,
    ) -> Result<crate::Variable, crate::SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, crate::SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        let var = self.cs.alloc_input(|| {
            f().map_err(|_| crate::SynthesisError::AssignmentMissing)
        }).map_err(|_| crate::SynthesisError::AssignmentMissing)?;

        Ok(match var {
            SonicVariable::A(index) => crate::Variable::new_unchecked(crate::Index::Input(index)),
            SonicVariable::B(index) => crate::Variable::new_unchecked(crate::Index::Aux(index)),
            _ => unreachable!(),
        })
    }

    fn enforce<A, AR, LA, LB, LC>(&mut self, _: A, a: LA, b: LB, c: LC)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
        LA: FnOnce(crate::LinearCombination<E>) -> crate::LinearCombination<E>,
        LB: FnOnce(crate::LinearCombination<E>) -> crate::LinearCombination<E>,
        LC: FnOnce(crate::LinearCombination<E>) -> crate::LinearCombination<E>,
    {
        fn convert<E: Engine>(lc: crate::LinearCombination<E>) -> SonicLinearCombination<E> {
            let mut ret = SonicLinearCombination::zero();

            for &(v, coeff) in lc.as_ref().iter() {
                let var = match v.get_unchecked() {
                    crate::Index::Input(i) => SonicVariable::A(i),
                    crate::Index::Aux(i) => SonicVariable::B(i),
                };

                ret = ret + (Coeff::Full(coeff), var);
            }

            ret
        }

        fn eval<E: Engine, CS: SonicConstraintSystem<E>>(
            lc: &SonicLinearCombination<E>,
            cs: &CS,
        ) -> Option<E::Fr> {
            let mut ret = E::Fr::zero();

            for &(v, coeff) in lc.as_ref().iter() {
                let mut tmp = match cs.get_value(v) {
                    Ok(tmp) => tmp,
                    Err(_) => return None,
                };
                coeff.multiply(&mut tmp);
                ret.add_assign(&tmp);
            }

            Some(ret)
        }

        let a_lc = convert(a(crate::LinearCombination::zero()));
        let a_value = eval(&a_lc, &*self.cs);
        let b_lc = convert(b(crate::LinearCombination::zero()));
        let b_value = eval(&b_lc, &*self.cs);
        let c_lc = convert(c(crate::LinearCombination::zero()));
        let c_value = eval(&c_lc, &*self.cs);

        let (a, b, c) = self
            .cs
            .multiply(|| Ok((a_value.unwrap(), b_value.unwrap(), c_value.unwrap())))
            .unwrap();

        self.cs.enforce_zero(a_lc - a);
        self.cs.enforce_zero(b_lc - b);
        self.cs.enforce_zero(c_lc - c);
    }

    fn push_namespace<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // Do nothing; we don't care about namespaces in this context.
    }

    fn pop_namespace(&mut self) {
        // Do nothing; we don't care about namespaces in this context.
    }

    fn get_root(&mut self) -> &mut Self::Root {
        self
    }
}

#[derive(Clone)]
pub struct AdaptorCircuit<T>(pub T);

impl<'a, E: Engine, C: crate::Circuit<E> + Clone> SonicCircuit<E> for AdaptorCircuit<C> {
    fn synthesize<CS: SonicConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        let mut adaptor = Adaptor {
            cs: cs,
            _marker: PhantomData,
        };

        match self.0.clone().synthesize(&mut adaptor) {
            Err(_) => return Err(SynthesisError::AssignmentMissing),
            Ok(_) => {}
        };

        Ok(())
    }
}