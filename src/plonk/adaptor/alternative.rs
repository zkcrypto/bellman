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

use std::collections::{HashSet, HashMap};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LcVariant {
    A,
    B,
    C,
}

// These are transpilation options over A * B - C = 0 constraint
#[derive(Clone, PartialEq, Eq)]
enum TranspilationVariant<E: Engine> {
    LeaveAsSingleVariable(E::Fr),
    IntoQuandaticGate((E::Fr, E::Fr, E::Fr)),
    IntoLinearGate((E::Fr, E::Fr)),
    IntoSingleAdditionGate((E::Fr, E::Fr, E::Fr, E::Fr)),
    IntoMultipleAdditionGates((E::Fr, E::Fr, E::Fr, E::Fr), Vec<E::Fr>),
    MergeLinearCombinations((LcVariant, E::Fr, Box<TranspilationVariant<E>>)),
    IsConstant(E::Fr), 
    TransformLc(Box<(TranspilationVariant<E>, TranspilationVariant<E>, TranspilationVariant<E>)>)
}

impl<E: Engine> std::fmt::Debug for TranspilationVariant<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TranspilationVariant::LeaveAsSingleVariable(c) => {
                writeln!(f, "Variant: leave LC as a single variable")?;
                writeln!(f, "With coefficient {}", c)?;
            },
            TranspilationVariant::IntoQuandaticGate(c) => {
                writeln!(f, "Variant: into quadratic gate")?;
                writeln!(f, "{} + {} * x + {} * x^2", c.0, c.1, c.2)?;
            },
            TranspilationVariant::IntoLinearGate(c) => {
                writeln!(f, "Variant: into linear gate")?;
                writeln!(f, "{} + {} * x", c.0, c.1)?;
            },
            TranspilationVariant::IntoSingleAdditionGate(c) => {
                writeln!(f, "Variant: into single addition gate")?;
                writeln!(f, "{}*a + {}*b + {}*c + {} = 0", c.0, c.1, c.2, c.3)?;
            },
            TranspilationVariant::IntoMultipleAdditionGates(c, next) => {
                writeln!(f, "Variant: into multiple addition gates")?;
                writeln!(f, "{}*a + {}*b + {}*c + {} = 0", c.0, c.1, c.2, c.3)?;
                writeln!(f, "{:?}", next)?;
            },
            TranspilationVariant::MergeLinearCombinations(c) => {
                writeln!(f, "Variant: merge linear combinations")?;
                writeln!(f, "Merge with hint: {:?}", c.0)?;
            },
            TranspilationVariant::IsConstant(c) => {
                writeln!(f, "Variant: into constant factor {}", c)?;
            },
            TranspilationVariant::TransformLc(b) => {
                writeln!(f, "Variant: into combinatoric transform LC")?;
                writeln!(f, "A: {:?}", b.as_ref().0)?;
                writeln!(f, "B: {:?}", b.as_ref().1)?;
                writeln!(f, "C: {:?}", b.as_ref().2)?;
            },
        }

        Ok(())
    }
}

pub struct Transpiler<E: Engine> {
    current_constraint_index: usize,
    current_plonk_input_idx: usize,
    current_plonk_aux_idx: usize,
    scratch: HashSet<crate::cs::Variable>,
    deduplication_scratch: HashMap<crate::cs::Variable, E::Fr>,
    hints: Vec<(usize, TranspilationVariant<E>)>,
}

impl<E: Engine> Transpiler<E> {
    pub fn new() -> Self {
        Self {
            current_constraint_index: 0,
            current_plonk_input_idx: 1,
            current_plonk_aux_idx: 0,
            scratch: HashSet::with_capacity((E::Fr::NUM_BITS * 2) as usize),
            deduplication_scratch: HashMap::with_capacity((E::Fr::NUM_BITS * 2) as usize),
            hints: vec![],
        }
    }

    fn increment_lc_number(&mut self) -> usize {
        let current_lc_number = self.current_constraint_index;
        self.current_constraint_index += 1;

        current_lc_number
    }

    fn rewrite_lc(&mut self, lc: &LinearCombination<E>, multiplier: E::Fr, free_term_constant: E::Fr) -> (Variable, TranspilationVariant<E>) {
        let one_fr = E::Fr::one();
        
        let (contains_constant, num_linear_terms) = num_unique_values::<E, Self>(&lc, &mut self.scratch);
        assert!(num_linear_terms > 0);
        if num_linear_terms == 1 && !contains_constant {
            let (existing_var, coeff) = lc.as_ref()[0];

            let hint = TranspilationVariant::<E>::LeaveAsSingleVariable(coeff);

            return (existing_var, hint);
        } else if num_linear_terms <= 2 {
            let (new_var, (mut a_coef, mut b_coef, mut c_coef, mut constant_coeff)) = rewrite_lc_into_single_addition_gate(&lc, self, &mut (self.scratch.clone()));

            if multiplier == E::Fr::zero() {
                assert!(free_term_constant == E::Fr::zero());
                // it's a constraint 0 * LC = 0
            } else {
                //scale
                if multiplier != one_fr {
                    a_coef.mul_assign(&multiplier);
                    b_coef.mul_assign(&multiplier);
                    c_coef.mul_assign(&multiplier);
                    constant_coeff.mul_assign(&multiplier);
                }

                constant_coeff.sub_assign(&free_term_constant);
            }
         
            let hint = TranspilationVariant::<E>::IntoSingleAdditionGate((a_coef, b_coef, c_coef, constant_coeff));

            return (new_var, hint);
        } else {
            let (new_var, first_gate, mut other_coefs) = rewrite_lc_into_multiple_addition_gates(&lc, self, &mut (self.scratch.clone()));
            let (mut a_coef, mut b_coef, mut c_coef, mut constant_coeff) = first_gate;
            if multiplier == E::Fr::zero() {
                assert!(free_term_constant == E::Fr::zero());
                // it's a constraint 0 * LC = 0
            } else {
                //scale
                if multiplier != one_fr {
                    a_coef.mul_assign(&multiplier);
                    b_coef.mul_assign(&multiplier);
                    c_coef.mul_assign(&multiplier);
                    constant_coeff.mul_assign(&multiplier);

                    for c in other_coefs.iter_mut() {
                        c.mul_assign(&multiplier);
                    }
                }

                constant_coeff.sub_assign(&free_term_constant);
            }

            let hint = TranspilationVariant::<E>::IntoMultipleAdditionGates((a_coef, b_coef, c_coef, constant_coeff), other_coefs);

            return (new_var, hint);
        }
    }
}

impl<E: Engine> crate::ConstraintSystem<E> for Transpiler<E>
{
    type Root = Self;


    fn one() -> crate::Variable {
        crate::Variable::new_unchecked(crate::Index::Input(1))
    }

    fn alloc<F, A, AR>(&mut self, _: A, _f: F) -> Result<crate::Variable, crate::SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, crate::SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        self.current_plonk_aux_idx += 1;

        Ok(crate::Variable::new_unchecked(crate::Index::Aux(self.current_plonk_aux_idx)))
    }

    fn alloc_input<F, A, AR>(
        &mut self,
        _: A,
        _f: F,
    ) -> Result<crate::Variable, crate::SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, crate::SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        self.current_plonk_input_idx += 1;

        Ok(crate::Variable::new_unchecked(crate::Index::Input(self.current_plonk_input_idx)))
    }

    fn enforce<A, AR, LA, LB, LC>(&mut self, _ann: A, a: LA, b: LB, c: LC)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
        LA: FnOnce(crate::LinearCombination<E>) -> crate::LinearCombination<E>,
        LB: FnOnce(crate::LinearCombination<E>) -> crate::LinearCombination<E>,
        LC: FnOnce(crate::LinearCombination<E>) -> crate::LinearCombination<E>,
    {
        let ann: String = _ann().into();
        println!("Enforce {}", ann);
        let zero_fr = E::Fr::zero();
        let one_fr = E::Fr::one();

        let mut negative_one_fr = E::Fr::one();
        negative_one_fr.negate();

        // we need to determine the type of transformation constraint

        // let's handle trivial cases first

        // A or B or C are just constant terms

        let a = deduplicate::<E, Self>(a(crate::LinearCombination::zero()), &mut self.deduplication_scratch);
        let b = deduplicate::<E, Self>(b(crate::LinearCombination::zero()), &mut self.deduplication_scratch);
        let c = deduplicate::<E, Self>(c(crate::LinearCombination::zero()), &mut self.deduplication_scratch);

        let (a_is_constant, a_constant_coeff) = is_constant::<E, Self>(&a);
        let (b_is_constant, b_constant_coeff) = is_constant::<E, Self>(&b);
        let (c_is_constant, c_constant_coeff) = is_constant::<E, Self>(&c);        

        match (a_is_constant, b_is_constant, c_is_constant) {
            (true, true, true) => {
                unreachable!("R1CS has a gate 1 * 1 = 1");
            },
            (true, false, true) | (false, true, true) => {
                // we have something like 1 * LC = 1
                let lc_ref = if !a_is_constant {
                    &a
                } else if !b_is_constant {
                    &b
                } else {
                    unreachable!()
                };

                let multiplier = if a_is_constant {
                    a_constant_coeff
                } else if b_is_constant {
                    b_constant_coeff
                } else {
                    unreachable!()
                };

                let current_lc_number = self.increment_lc_number();

                let (_, hint) = self.rewrite_lc(&lc_ref, multiplier, c_constant_coeff);

                println!("Hint = {:?}", hint);

                self.hints.push((current_lc_number, hint));

            },
            (false, false, true) => {                
                // potential quadatic gate
                let (is_quadratic_gate, coeffs) = is_quadratic_gate::<E, Self>(&a, &b, &c, &mut self.scratch);
                if is_quadratic_gate {
                    let current_lc_number = self.increment_lc_number();

                    let hint = TranspilationVariant::<E>::IntoQuandaticGate(coeffs);

                    println!("Hint = {:?}", hint);

                    self.hints.push((current_lc_number, hint));

                    return;
                }

                let (_new_a_var, hint_a) = self.rewrite_lc(&a, one_fr, zero_fr);
                let (_new_b_var, hint_b) = self.rewrite_lc(&b, one_fr, zero_fr);

                let current_lc_number = self.increment_lc_number();

                let hint_c = TranspilationVariant::<E>::IsConstant(c_constant_coeff);

                let hint = TranspilationVariant::<E>::TransformLc(Box::new((hint_a, hint_b, hint_c)));

                println!("Hint = {:?}", hint);

                self.hints.push((current_lc_number, hint));

            },
            (true, false, false) | (false, true, false) => {
                // LC * 1 = LC

                let multiplier = if a_is_constant {
                    a_constant_coeff
                } else if b_is_constant {
                    b_constant_coeff
                } else {
                    unreachable!()
                };

                let lc_variant = if a_is_constant {
                    LcVariant::A
                } else {
                    LcVariant::B
                };

                if multiplier == zero_fr {
                    // LC_0 * 0 = LC => LC = 0
                    let lc_ref = if !a_is_constant {
                        &a
                    } else if !b_is_constant {
                        &b
                    } else {
                        unreachable!()
                    };

                    let (_new_var, hint_lc) = self.rewrite_lc(&lc_ref, multiplier, zero_fr);

                    let current_lc_number = self.increment_lc_number();

                    let hint = TranspilationVariant::<E>::MergeLinearCombinations((lc_variant, multiplier, Box::new(hint_lc)));

                    println!("Hint = {:?}", hint);

                    self.hints.push((current_lc_number, hint));

                    return;
                }

                let mut final_lc = if !a_is_constant {
                    a
                } else if !b_is_constant {
                    b
                } else {
                    unreachable!()
                };

                if multiplier != one_fr {
                    for (_, c) in final_lc.0.iter_mut() {
                        c.mul_assign(&multiplier);
                    }
                }

                let final_lc = final_lc - &c;

                let (_new_var, hint_lc) = self.rewrite_lc(&final_lc, one_fr, zero_fr);

                let current_lc_number = self.increment_lc_number();

                let hint = TranspilationVariant::<E>::MergeLinearCombinations((lc_variant, multiplier, Box::new(hint_lc)));

                println!("Hint = {:?}", hint);

                self.hints.push((current_lc_number, hint));

                return;

            },
            (true, true, false) => {
                let mut final_constant = a_constant_coeff;
                final_constant.mul_assign(&b_constant_coeff);

                let (_new_var, hint_lc) = self.rewrite_lc(&c, one_fr, final_constant);

                let current_lc_number = self.increment_lc_number();

                let hint = TranspilationVariant::<E>::MergeLinearCombinations((LcVariant::C, one_fr, Box::new(hint_lc)));

                println!("Hint = {:?}", hint);

                self.hints.push((current_lc_number, hint));

            },
            (false, false, false) => {
                // potentially it can still be quadratic
                let (is_quadratic_gate, coeffs) = is_quadratic_gate::<E, Self>(&a, &b, &c, &mut self.scratch);
                if is_quadratic_gate {
                    let current_lc_number = self.increment_lc_number();

                    let hint = TranspilationVariant::<E>::IntoQuandaticGate(coeffs);

                    println!("Hint = {:?}", hint);

                    self.hints.push((current_lc_number, hint));

                    return;
                }

                // rewrite into addition gates and multiplication gates
                
                let (_new_a_var, hint_a) = self.rewrite_lc(&a, one_fr, zero_fr);
                let (_new_b_var, hint_b) = self.rewrite_lc(&b, one_fr, zero_fr);
                let (_new_c_var, hint_c) = self.rewrite_lc(&c, one_fr, zero_fr);

                let current_lc_number = self.increment_lc_number();

                let hint = TranspilationVariant::<E>::TransformLc(Box::new((hint_a, hint_b, hint_c)));

                println!("Hint = {:?}", hint);

                self.hints.push((current_lc_number, hint));
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

// List of heuristics

use crate::{LinearCombination, ConstraintSystem, Variable};

fn is_quadratic_gate<E: Engine, CS: ConstraintSystem<E>>(
    a: &LinearCombination<E>, 
    b: &LinearCombination<E>, 
    c: &LinearCombination<E>,
    scratch: &mut HashSet::<crate::cs::Variable>
) -> (bool, (E::Fr, E::Fr, E::Fr)) {
    let zero = E::Fr::zero();
    
    let (_a_containts_constant, a_constant_coeff) = get_constant_term::<E, CS>(&a);
    let (_b_containts_constant, b_constant_coeff) = get_constant_term::<E, CS>(&b);
    let (_c_containts_constant, c_constant_coeff) = get_constant_term::<E, CS>(&c);

    let (a_is_linear, a_linear_var, a_linear_var_coeff) = is_linear_term::<E, CS>(&a, scratch);
    let (b_is_linear, b_linear_var, b_linear_var_coeff) = is_linear_term::<E, CS>(&b, scratch);
    let (c_is_linear, c_linear_var, c_linear_var_coeff) = is_linear_term::<E, CS>(&c, scratch);

    let (c_is_constant, _) = is_constant::<E, CS>(&c);

    let mut is_quadratic = false;
    if c_is_constant {
        is_quadratic = a_is_linear && b_is_linear && a_linear_var == b_linear_var;
    } else {
        if a_is_linear && b_is_linear && c_is_linear && a_linear_var == b_linear_var && b_linear_var == c_linear_var {
            is_quadratic = true;
        } else {
            return (false, (zero, zero, zero));
        }
    }

    if is_quadratic {
        // something like (v - 1) * (v - 1) = (v - 1)
        // and we can make a quadratic gate

        let mut quadratic_term = a_linear_var_coeff;
        quadratic_term.mul_assign(&b_linear_var_coeff);

        let mut linear_term_0 = a_constant_coeff;
        linear_term_0.mul_assign(&b_linear_var_coeff);

        let mut linear_term_1 = b_constant_coeff;
        linear_term_1.mul_assign(&a_linear_var_coeff);

        let mut linear_term = linear_term_0;
        linear_term.add_assign(&linear_term_1);
        if c_is_linear {
            linear_term.sub_assign(&c_linear_var_coeff);
        }

        let mut constant_term = a_constant_coeff;
        constant_term.mul_assign(&b_constant_coeff);

        if c_constant_coeff != zero {
            constant_term.sub_assign(&c_constant_coeff);
        }

        return (true, (constant_term, linear_term, quadratic_term));
    } 

    (false, (zero, zero, zero))
}

fn is_constant<E: Engine, CS: ConstraintSystem<E>>(lc: &LinearCombination<E>) -> (bool, E::Fr) {
    // formally it's an empty LC, so it's a constant 0
    if lc.as_ref().len() == 0 {
        return (true, E::Fr::zero());
    }
    
    let result = get_constant_term::<E, CS>(&lc);

    if result.0 && lc.as_ref().len() == 1 {
        return result;
    }

    (false, E::Fr::zero())
}

fn get_constant_term<E: Engine, CS: ConstraintSystem<E>>(lc: &LinearCombination<E>) -> (bool, E::Fr) {
    let cs_one = CS::one();
    
    for (var, coeff) in lc.as_ref().iter() {
        if var == &cs_one {
            return (true, *coeff);
        }
    }

    (false, E::Fr::zero())
}


fn num_unique_values<E: Engine, CS: ConstraintSystem<E>>(lc: &LinearCombination<E>, scratch: &mut HashSet::<crate::cs::Variable>) -> (bool, usize) {
    let cs_one = CS::one();

    debug_assert!(scratch.is_empty());
    
    let mut contains_constant = false;

    for (var, _) in lc.as_ref().iter() {
        if var != &cs_one {
            scratch.insert(*var);
        } else {
            contains_constant = true;
        }
    }

    let num_unique_without_constant = scratch.len();

    scratch.clear();

    (contains_constant, num_unique_without_constant)
}

fn is_linear_term<E: Engine, CS: ConstraintSystem<E>>(lc: &LinearCombination<E>, scratch: &mut HashSet::<crate::cs::Variable>) -> (bool, Variable, E::Fr) {
    let cs_one = CS::one();

    debug_assert!(scratch.is_empty());
    
    let mut linear_coeff = E::Fr::zero();

    for (var, coeff) in lc.as_ref().iter() {
        if var != &cs_one {
            scratch.insert(*var);
            linear_coeff = *coeff;
        }
    }

    let num_unique_without_constant = scratch.len();

    if num_unique_without_constant == 1 {
        let terms: Vec<_> = scratch.drain().collect();
        let term = terms[0];

        return (true, term, linear_coeff)
    } else {
        scratch.clear();

        return (false, cs_one, E::Fr::zero())
    }    
}

fn rewrite_lc_into_single_addition_gate<E: Engine, CS: ConstraintSystem<E>>(
    lc: &LinearCombination<E>,
    cs: &mut CS,
    scratch: &mut HashSet<crate::cs::Variable>
) -> (Variable, (E::Fr, E::Fr, E::Fr, E::Fr)) {
    let (_contains_constant, num_linear_terms) = num_unique_values::<E, CS>(&lc, scratch);
    assert!(num_linear_terms > 0 && num_linear_terms <= 2);

    // we can just make an addition gate
    let cs_one = CS::one();

    let mut constant_term = E::Fr::zero();

    let mut found_a = false;
    let mut a_coeff = E::Fr::zero();
    let mut b_coeff = E::Fr::zero();

    let it = lc.as_ref().iter();

    for (var, coeff) in it {
        if var == &cs_one {
            constant_term = *coeff;
        } else {
            if !found_a {
                found_a = true;
                a_coeff = *coeff;
            } else {
                b_coeff = *coeff;
            }
        }
    }

    let mut c_coeff = E::Fr::one();
    c_coeff.negate();

    let new_var = cs.alloc(|| "allocate addition gate", 
    || {
        unreachable!()
    }).expect("must allocate an extra variable");

    (new_var, (a_coeff, b_coeff, c_coeff, constant_term))
}

fn rewrite_lc_into_multiple_addition_gates<E: Engine, CS: ConstraintSystem<E>>(
    lc: &LinearCombination<E>,
    cs: &mut CS,
    scratch: &mut HashSet<crate::cs::Variable>
) -> (Variable, (E::Fr, E::Fr, E::Fr, E::Fr), Vec<E::Fr>) // first rewrite is full, than it's Z + a * X - Y = 0
{
    assert!(lc.as_ref().len() > 2);

    let (_contains_constant, num_linear_terms) = num_unique_values::<E, CS>(&lc, scratch);
    assert!(num_linear_terms > 2);
    // we can just make an addition gate
    let cs_one = CS::one();

    let (_, constant_term) = get_constant_term::<E, CS>(&lc);

    let mut found_a = false;

    let mut a_coeff = E::Fr::zero();
    let mut b_coeff = E::Fr::zero();

    let mut it = lc.as_ref().iter();

    for (var, coeff) in &mut it {
        if var != &cs_one {
            if !found_a {
                found_a = true;
                a_coeff = *coeff;
            } else {
                b_coeff = *coeff;
                break;
            }
        }
    }

    // we've consumed 2 values

    let mut c_coeff = E::Fr::one();
    c_coeff.negate();

    let mut new_var = cs.alloc(|| "allocate addition gate", 
        || {
            unreachable!()
        }
    ).expect("must allocate an extra variable");

    let first_addition_gate = (a_coeff, b_coeff, c_coeff, constant_term);

    let mut extra_coefficients = Vec::with_capacity(lc.as_ref().len() - 2);
    for (var, coeff) in it {
        if var != &cs_one {
            extra_coefficients.push(*coeff);
            new_var = cs.alloc(|| "allocate addition gate", 
                || {
                    unreachable!()
                }
            ).expect("must allocate an extra variable");
        }
    }

    (new_var, first_addition_gate, extra_coefficients)
}

fn deduplicate<E: Engine, CS: ConstraintSystem<E>>(
    lc: LinearCombination<E>,
    scratch: &mut HashMap<crate::cs::Variable, E::Fr>
) -> LinearCombination<E> {
    assert!(scratch.is_empty());

    for (var, coeff) in lc.0.into_iter() {
        if let Some(existing_coeff) = scratch.get_mut(&var) {
            existing_coeff.add_assign(&coeff);
        } else {
            scratch.insert(var, coeff);
        }
    }

    let as_vec: Vec<(Variable, E::Fr)> = scratch.drain().collect();

    LinearCombination(as_vec)
}



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