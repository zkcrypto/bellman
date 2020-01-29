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

pub mod alternative;

// pub struct Adaptor<'a, E: Engine, CS: PlonkConstraintSystem<E> + 'a> {
//     cs: &'a mut CS,
//     _marker: PhantomData<E>,
// }

// impl<'a, E: Engine, CS: PlonkConstraintSystem<E> + 'a> crate::ConstraintSystem<E>
//     for Adaptor<'a, E, CS>
// {
//     type Root = Self;

//     fn one() -> crate::Variable {
//         crate::Variable::new_unchecked(crate::Index::Input(0))
//     }

//     fn alloc<F, A, AR>(&mut self, _: A, f: F) -> Result<crate::Variable, crate::SynthesisError>
//     where
//         F: FnOnce() -> Result<E::Fr, crate::SynthesisError>,
//         A: FnOnce() -> AR,
//         AR: Into<String>,
//     {
//         let var = self.cs.alloc(|| {
//             f().map_err(|_| crate::SynthesisError::AssignmentMissing)
//         })?;

//         Ok(match var {
//             PlonkVariable(PlonkIndex::Input(index)) => crate::Variable::new_unchecked(crate::Index::Input(index)),
//             _ => unreachable!(),
//         })
//     }

//     fn alloc_input<F, A, AR>(
//         &mut self,
//         _: A,
//         f: F,
//     ) -> Result<crate::Variable, crate::SynthesisError>
//     where
//         F: FnOnce() -> Result<E::Fr, crate::SynthesisError>,
//         A: FnOnce() -> AR,
//         AR: Into<String>,
//     {
//         let var = self.cs.alloc_input(|| {
//             f().map_err(|_| crate::SynthesisError::AssignmentMissing)
//         })?;

//         Ok(match var {
//             PlonkVariable(PlonkIndex::Aux(index)) => crate::Variable::new_unchecked(crate::Index::Aux(index)),
//             _ => unreachable!(),
//         })
//     }

//     fn enforce<A, AR, LA, LB, LC>(&mut self, _: A, a: LA, b: LB, c: LC)
//     where
//         A: FnOnce() -> AR,
//         AR: Into<String>,
//         LA: FnOnce(crate::LinearCombination<E>) -> crate::LinearCombination<E>,
//         LB: FnOnce(crate::LinearCombination<E>) -> crate::LinearCombination<E>,
//         LC: FnOnce(crate::LinearCombination<E>) -> crate::LinearCombination<E>,
//     {
        
//         /// Represents either a "true" variable or a constant
//         /// auxillary variable.
//         #[derive(Copy, Clone, PartialEq, Debug, Hash, Eq)]
//         enum Var
//         {
//             InputVar(PlonkVariable),
//             ConstVar
//         }
        
//         fn convert<E: Engine>(lc: crate::LinearCombination<E>) -> Vec<(E::Fr, Var)> {
//             let mut ret = Vec::with_capacity(lc.as_ref().len());

//             for &(v, coeff) in lc.as_ref().iter() {
//                 let var = match v.get_unchecked() {
//                     crate::Index::Input(0) => Var::ConstVar,
//                     crate::Index::Input(i) => Var::InputVar(PlonkVariable(PlonkIndex::Input(i))),
//                     crate::Index::Aux(i) => Var::InputVar(PlonkVariable(PlonkIndex::Aux(i))),
//                 };

//                 ret.push((coeff, var));
//             }

//             ret
//         }

//         let a_terms = convert(a(crate::LinearCombination::zero()));
//         let b_terms = convert(b(crate::LinearCombination::zero()));
//         let c_terms = convert(c(crate::LinearCombination::zero()));

//         ///first check if we are dealing with a boolean constraint
//         ///we use the following euristics: 
//         ///analyse comment string 
//         ///calculate the number of arguments in each linear combination - in boolean constraint length of each lc is at most 2
//         /// this function returns true in the case of boolean constraint
        
//         fn handle_boolean_constraint<A, AR, E: Engine>(
//             la: &Vec<(E::Fr, Var)>,
//             lb: &Vec<(E::Fr, Var)>,
//             lc: &Vec<(E::Fr, Var)>,
//         ) -> bool
//         where
//             A: FnOnce() -> AR,
//             AR: Into<String>
//         {
//             return true;
//         }
        

//         fn eval_lc_short<E: Engine, CS: PlonkConstraintSystem<E>>(
//             term1: (E::Fr, PlonkVariable),
//             term2: (E::Fr, PlonkVariable),
//             cs: &CS,
//         ) -> Option<E::Fr>
//         {
//             let mut extra_value = E::Fr::zero();

//             let mut var_value = match cs.get_value(term1.1) {
//                 Ok(tmp) => tmp,
//                 Err(_) => return None,
//             };
//             var_value.mul_assign(&term1.0);
//             extra_value.add_assign(&var_value);

//             var_value = match cs.get_value(term2.1) {
//                 Ok(tmp) => tmp,
//                 Err(_) => return None,
//             };
//             var_value.mul_assign(&term2.0);
//             extra_value.add_assign(&var_value);

//             Some(extra_value)
//         }


//         fn allocate_new_lc_var<E: Engine, CS: PlonkConstraintSystem<E>>(
//             term1: (E::Fr, PlonkVariable),
//             term2: (E::Fr, PlonkVariable),
//             cs: &mut CS,
//         ) -> PlonkVariable
//         {
            
//             let extra_value = eval_lc_short(term1, term2, &*cs);
//             let extra_variable = cs.alloc(||
//                 {
//                     if let Some(value) = extra_value {
//                         Ok(value)
//                     } else {
//                         Err(SynthesisError::AssignmentMissing)
//                     }
//                 }
//                 ).expect("must allocate");
            
//             cs.enforce_mul_3((term1.1, term2.1, extra_variable)).expect("must allocate");
//             extra_variable
//         }


//         fn allocate_lc_intermediate_variables<E: Engine, CS: PlonkConstraintSystem<E>>(
//             terms: Vec<(E::Fr, Var)>, 
//             cs: &mut CS,
//         ) -> (PlonkVariable, Option<E::Fr>) {
            
//             debug_assert!(terms.len() > 2);
//             let mut const_var_found = false;
//             let mut const_coeff = E::Fr::zero();
//             let mut current_var : Option<(E::Fr, PlonkVariable)> = None;

//             for &(coeff, var) in terms.iter() {
//                 match var {
//                     Var::ConstVar => {
//                         if const_var_found {
//                             unreachable!();
//                         }
//                         const_var_found = true;
//                         const_coeff = coeff;
//                     }
//                     Var::InputVar(pv) => {
//                         current_var = match current_var {
//                             None => Some((coeff, pv)),
//                             Some((old_coeff, old_pv)) => {
//                                 let new_val = allocate_new_lc_var((old_coeff, old_pv), (coeff, pv), cs);
//                                 Some((E::Fr::one(), new_val))
//                             }
//                         }
//                     }                  
//                 }

//             }

//             let var = match current_var {
//                 Some((_, pv)) => pv,
//                 None => unreachable!(),
//             };

//             let coef = match const_var_found{
//                 false => None,
//                 true => Some(const_coeff)
//             } ;

//             return (var, coef)         
//         }

                    
//         /// after parsing we should return on of three possible results: 
//         /// variable, constant or sum variable + constant
        
//         fn parse_lc<E: Engine, CS: PlonkConstraintSystem<E>>(
//             terms: Vec<(E::Fr, Var)>,
//             cs: &mut CS,
//         ) -> (Option<(E::Fr, PlonkVariable)>, Option<E::Fr>) {
//             // there are few options
//             match terms.len() {
//                 0 => {
//                     //Every linear combination in real cs should contain at least one term!
//                     unreachable!();
//                 },

//                 1 => {
//                     let (c_0, v_0) = terms[0];
//                     let result = match v_0 {
//                         Var::InputVar(pv) => (Some((c_0, pv)), None),
//                         Var::ConstVar => (None, Some(c_0)),
//                     };
//                     // forward the result
//                     return result;
//                 },

//                 2 => {
//                     let (c_0, v_0) = terms[0];
//                     let (c_1, v_1) = terms[1];
                    
//                     //check of one of v_0, v_1 is constant and the other is variable or vice versa
//                     //the case of two constants is impossible in real cs!
//                     let result = match (v_0, v_1) {
//                         (Var::InputVar(pv), Var::ConstVar) => (Some((c_0, pv)), Some(c_1)),
//                         (Var::ConstVar, Var::InputVar(pv)) => (Some((c_1, pv)), Some(c_0)),
//                         (Var::InputVar(pv0), Var::InputVar(pv1)) => {
//                             let extra_variable = allocate_new_lc_var((c_0, pv0), (c_1, pv1), cs);
//                             (Some((E::Fr::one(), extra_variable)), None)    
//                             }
//                         (Var::ConstVar, Var::ConstVar) => unreachable!(),
//                     };

//                     return result;
//                 }

//                 _ => {
//                     // here we need to allocate intermediate variables and output the last one
//                     let last_vars = allocate_lc_intermediate_variables(terms, cs);
//                     return (Some((E::Fr::one(), last_vars.0)), last_vars.1);                
//                 }                  
//             }
//         }

//         let a_var = parse_lc(a_terms, self.cs);
//         let b_var = parse_lc(b_terms, self.cs);
//         let c_var = parse_lc(c_terms, self.cs);


//         /// parse result and return expr of the form: coeff * var + constant

//         fn unfold_var<E: Engine, CS: PlonkConstraintSystem<E>>(
//             var: (Option<(E::Fr, PlonkVariable)>, Option<(E::Fr)>),
//             stub: PlonkVariable,
//             cs: &mut CS,
//         ) -> (E::Fr, PlonkVariable, E::Fr)
//         {
            
//             let result = match var {
//                 (Some((coeff, var)), Some(constant)) => (coeff, var, constant),
//                 (Some((coeff, var)), None) => (coeff, var, E::Fr::zero()),
//                 (None, Some(constant)) => (E::Fr::zero(), stub, constant), 
//                 _ => unreachable!(),
//             };

//             return result;
//         }

//         // our final equation is of the following form
//         // (x a_var + c_1) (y b_var + c_2) = (z c_var + c_3)
//         // we can convert it to standard PLONK form: 
//         // (xy) a_var + b_var + (x c_2) a_var + (y c_1) b_var - z c_var + (c_1 c_2 - c_3) */

//         let (mut x, a_var, mut c_1) : (E::Fr, PlonkVariable, E::Fr) = unfold_var(a_var, CS::ZERO, self.cs);
//         let (mut y, b_var, c_2) : (E::Fr, PlonkVariable, E::Fr) = unfold_var(b_var, CS::ZERO, self.cs);
//         let (mut z, c_var, mut c_3) : (E::Fr, PlonkVariable, E::Fr) = unfold_var(c_var, CS::ZERO, self.cs);

//         let mut a_coef : E::Fr = x;
//         a_coef.mul_assign(&y);

//         x.mul_assign(&c_2);
//         y.mul_assign(&c_1);
//         z.negate();
//         c_1.mul_assign(&c_2);
//         c_3.negate();
//         c_1.add_assign(&c_3);

//         self.cs.new_gate((a_var, b_var, c_var), (a_coef, x, y, z, c_1));    
//     }

//     fn push_namespace<NR, N>(&mut self, _: N)
//     where
//         NR: Into<String>,
//         N: FnOnce() -> NR,
//     {
//         // Do nothing; we don't care about namespaces in this context.
//     }

//     fn pop_namespace(&mut self) {
//         // Do nothing; we don't care about namespaces in this context.
//     }

//     fn get_root(&mut self) -> &mut Self::Root {
//         self
//     }
// }

// #[derive(Clone)]
// pub struct AdaptorCircuit<T>(pub T);

// impl<'a, E: Engine, C: crate::Circuit<E> + Clone> PlonkCircuit<E> for AdaptorCircuit<C> {
//     fn synthesize<CS: PlonkConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
//         let mut adaptor = Adaptor {
//             cs: cs,
//             _marker: PhantomData,
//         };

//         match self.0.clone().synthesize(&mut adaptor) {
//             Err(_) => return Err(SynthesisError::AssignmentMissing),
//             Ok(_) => {}
//         };

//         Ok(())
//     }
// }