use crate::pairing::ff::{Field, PrimeField};
use crate::pairing::{Engine};

use crate::SynthesisError;

use crate::plonk::cs::gates::Gate;
use crate::plonk::cs::gates::Coeff;
use crate::plonk::cs::gates::Variable as PlonkVariable;
use crate::plonk::cs::gates::Index as PlonkIndex;

use crate::plonk::cs::Circuit as PlonkCircuit;
use crate::plonk::cs::ConstraintSystem as PlonkConstraintSystem;

use std::marker::PhantomData;

pub struct Adaptor<'a, E: Engine, CS: PlonkConstraintSystem<E> + 'a> {
    cs: &'a mut CS,
    _marker: PhantomData<E>,
}

impl<'a, E: Engine, CS: PlonkConstraintSystem<E> + 'a> crate::ConstraintSystem<E>
    for Adaptor<'a, E, CS>
{
    type Root = Self;


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
        })?;

        Ok(match var {
            PlonkVariable(PlonkIndex::Input(index)) => crate::Variable::new_unchecked(crate::Index::Input(index)),
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
        })?;

        Ok(match var {
            PlonkVariable(PlonkIndex::Aux(index)) => crate::Variable::new_unchecked(crate::Index::Aux(index)),
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
        let mut negative_one = E::Fr::one();
        negative_one.negate();

        fn convert<E: Engine>(lc: crate::LinearCombination<E>) -> Vec<(E::Fr, PlonkVariable)> {
            let mut ret = Vec::with_capacity(lc.as_ref().len());

            for &(v, coeff) in lc.as_ref().iter() {
                let var = match v.get_unchecked() {
                    crate::Index::Input(i) => PlonkVariable(PlonkIndex::Input(i)),
                    crate::Index::Aux(i) => PlonkVariable(PlonkIndex::Aux(i)),
                };

                ret.push((coeff, var));
            }

            ret
        }

        fn eval_short<E: Engine, CS: PlonkConstraintSystem<E>>(
            terms: &Vec<(E::Fr, PlonkVariable)>,
            cs: &CS,
        ) -> Option<E::Fr> {
            debug_assert!(terms.len() < 3 && terms.len() > 0);
            let mut extra_value = E::Fr::zero();

            for &(coeff, var) in terms.iter() {
                let mut var_value = match cs.get_value(var) {
                    Ok(tmp) => tmp,
                    Err(_) => return None,
                };
                var_value.mul_assign(&coeff);

                extra_value.add_assign(&var_value);
            }

            Some(extra_value)
        }

        fn eval<E: Engine, CS: PlonkConstraintSystem<E>>(
            terms: &Vec<(E::Fr, PlonkVariable)>,
            cs: &CS,
        ) -> Option<Vec<E::Fr>> {
            debug_assert!(terms.len() >= 3);

            let mut new_values = Vec::with_capacity(terms.len() - 1);
            let mut iter = terms.iter();

            let &(coeff_0, var) = iter.next().unwrap();
            let mut var_0_value = match cs.get_value(var) {
                Ok(tmp) => tmp,
                Err(_) => return None,
            };
            var_0_value.mul_assign(&coeff_0);

            let &(coeff_1, var) = iter.next().unwrap();
            let mut var_1_value = match cs.get_value(var) {
                Ok(tmp) => tmp,
                Err(_) => return None,
            };
            var_1_value.mul_assign(&coeff_1);

            let mut new_var_value = var_0_value;
            new_var_value.add_assign(&var_1_value);

            new_values.push(new_var_value);

            for &(coeff, var) in iter {
                let mut ret = new_var_value;
                let mut var_value = match cs.get_value(var) {
                    Ok(tmp) => tmp,
                    Err(_) => return None,
                };
                var_value.mul_assign(&coeff);
                ret.add_assign(&var_value);

                new_values.push(var_value);
                new_var_value = var_value;
            }

            Some(new_values)
        }

        fn allocate_lc_intermediate_variables<E: Engine, CS: PlonkConstraintSystem<E>>(
            original_terms: Vec<(E::Fr, PlonkVariable)>, 
            intermediate_values: Option<Vec<E::Fr>>,
            cs: &mut CS,
        ) -> PlonkVariable {
            let new_variables = if let Some(values) = intermediate_values {
                debug_assert!(values.len() == original_terms.len() - 1);

                let new_variables: Vec<_> = values.into_iter().map(|v| 
                    cs.alloc(
                        || Ok(v)
                    ).expect("must allocate")
                ).collect();

                new_variables
            } else {
                let new_variables: Vec<_> = (0..(original_terms.len() - 1)).map(|_| 
                    cs.alloc(
                        || Err(SynthesisError::AssignmentMissing)
                    ).expect("must allocate")
                ).collect();

                new_variables
            };

            let mut original_iter = original_terms.into_iter();
            let mut new_iter = new_variables.into_iter();

            let mut intermediate_var = new_iter.next().expect("there is at least one new variable");

            let (c_0, v_0) = original_iter.next().expect("there is at least one old variable");
            let (c_1, v_1) = original_iter.next().expect("there are at least two old variables");

            let mut negative_one = E::Fr::one();
            negative_one.negate();

            let one = E::Fr::one();

            cs.enforce_zero_3((v_0, v_1, intermediate_var), (c_0, c_1, negative_one)).expect("must enforce");

            debug_assert!(new_iter.len() == original_iter.len());

            let remaining = new_iter.len();

            for _ in 0..remaining {
                let (coeff, original_var) = original_iter.next().expect("there is at least one more old variable");
                let new_var = new_iter.next().expect("there is at least one more new variable");
                cs.enforce_zero_3((original_var, intermediate_var, new_var), (coeff, one, negative_one)).expect("must enforce");

                intermediate_var = new_var;
            }

            intermediate_var
        }

        let a_terms = convert(a(crate::LinearCombination::zero()));
        let b_terms = convert(b(crate::LinearCombination::zero()));
        let c_terms = convert(c(crate::LinearCombination::zero()));

        fn enforce<E: Engine, CS: PlonkConstraintSystem<E>>(
            terms: Vec<(E::Fr, PlonkVariable)>,
            cs: &mut CS,
        ) -> Option<PlonkVariable> {
            // there are few options
            match terms.len() {
                0 => {
                    // - no terms, so it's zero and we should later make a gate that basically constraints a*0 = 0
                    None
                },
                1 => {
                    let (c_0, v_0) = terms[0];
                    if c_0 == E::Fr::one() {
                        // if factor is one then we can just forwrad the variable
                        return Some(v_0);
                    }
                    // make a single new variable that has coefficient of minus one
                    let mut coeff = E::Fr::one();
                    coeff.negate();
                    let extra_value = eval_short(&terms, &*cs);
                    let extra_variable = cs.alloc(||
                    {
                        if let Some(value) = extra_value {
                            Ok(value)
                        } else {
                            Err(SynthesisError::AssignmentMissing)
                        }
                    }
                    ).expect("must allocate");
                    
                    cs.enforce_zero_2((v_0, extra_variable), (c_0, coeff)).expect("must enforce");
                    Some(extra_variable)
                },
                2 => {
                    // make a single new variable that has coefficient of minus one
                    let mut coeff = E::Fr::one();
                    coeff.negate();
                    let extra_value = eval_short(&terms, &*cs);
                    let extra_variable = cs.alloc(||
                    {
                        if let Some(value) = extra_value {
                            Ok(value)
                        } else {
                            Err(SynthesisError::AssignmentMissing)
                        }
                    }
                    ).expect("must allocate");
                    let (c_0, v_0) = terms[0];
                    let (c_1, v_1) = terms[1];
                    cs.enforce_zero_3((v_0, v_1, extra_variable), (c_0, c_1, coeff)).expect("must enforce");
                    Some(extra_variable)
                },
                _ => {
                    // here we need to allocate intermediate variables and output the last one
                    let intermediate_values = eval(&terms, &*cs);
                    let last_variable = allocate_lc_intermediate_variables(
                        terms,
                        intermediate_values, 
                        cs
                    );

                    Some(last_variable)
                }
            }
        }

        let a_var = enforce(a_terms, self.cs);
        let b_var = enforce(b_terms, self.cs);
        let c_var = enforce(c_terms, self.cs);

        match (a_var, b_var, c_var) {
            (Some(var), None, None) | (None, Some(var), None) | (None, None, Some(var)) => {
                self.cs.enforce_constant(var, E::Fr::zero()).expect("must enforce");
            },

            (Some(var_0), Some(var_1), None) | (None, Some(var_0), Some(var_1)) | (Some(var_0), None, Some(var_1)) => {
                self.cs.enforce_mul_2((var_0, var_1)).expect("must enforce");
            },

            (Some(var_0), Some(var_1), Some(var_2)) => {
                self.cs.enforce_mul_3((var_0, var_1, var_2)).expect("must enforce");
            },
            _ => {
                unreachable!()
            }
        }        
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

impl<'a, E: Engine, C: crate::Circuit<E> + Clone> PlonkCircuit<E> for AdaptorCircuit<C> {
    fn synthesize<CS: PlonkConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
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