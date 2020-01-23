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
pub enum LcVariant {
    A,
    B,
    C,
}

// These are transpilation options over A * B - C = 0 constraint
#[derive(Clone, PartialEq, Eq)]
pub enum TranspilationVariant<E: Engine> {
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
    // deduplication_scratch: HashMap<crate::cs::Variable, E::Fr>,
    deduplication_scratch: HashMap<crate::cs::Variable, usize>,
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
                unreachable!();
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
        // let ann: String = _ann().into();
        // println!("Enforce {}", ann);
        let zero_fr = E::Fr::zero();
        let one_fr = E::Fr::one();

        let mut negative_one_fr = E::Fr::one();
        negative_one_fr.negate();

        // we need to determine the type of transformation constraint

        // let's handle trivial cases first

        // A or B or C are just constant terms

        let a = deduplicate_stable::<E, Self>(a(crate::LinearCombination::zero()), &mut self.deduplication_scratch);
        let b = deduplicate_stable::<E, Self>(b(crate::LinearCombination::zero()), &mut self.deduplication_scratch);
        let c = deduplicate_stable::<E, Self>(c(crate::LinearCombination::zero()), &mut self.deduplication_scratch);

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

                // println!("Hint = {:?}", hint);

                self.hints.push((current_lc_number, hint));

            },
            (false, false, true) => {                
                // potential quadatic gate
                let (is_quadratic_gate, coeffs) = is_quadratic_gate::<E, Self>(&a, &b, &c, &mut self.scratch);
                if is_quadratic_gate {
                    let current_lc_number = self.increment_lc_number();

                    let hint = TranspilationVariant::<E>::IntoQuandaticGate(coeffs);

                    // println!("Hint = {:?}", hint);

                    self.hints.push((current_lc_number, hint));

                    return;
                }

                let (_new_a_var, hint_a) = self.rewrite_lc(&a, one_fr, zero_fr);
                let (_new_b_var, hint_b) = self.rewrite_lc(&b, one_fr, zero_fr);

                let current_lc_number = self.increment_lc_number();

                let hint_c = TranspilationVariant::<E>::IsConstant(c_constant_coeff);

                let hint = TranspilationVariant::<E>::TransformLc(Box::new((hint_a, hint_b, hint_c)));

                // println!("Hint = {:?}", hint);

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
                    // LC_AB * 0 = LC_C => LC_C == 0

                    // unimplemented!();

                    // let lc_ref = if !a_is_constant {
                    //     &a
                    // } else if !b_is_constant {
                    //     &b
                    // } else {
                    //     unreachable!()
                    // };

                    // let (_new_var, hint_lc) = self.rewrite_lc(&lc_ref, multiplier, zero_fr);

                    // let current_lc_number = self.increment_lc_number();

                    // let hint = TranspilationVariant::<E>::MergeLinearCombinations((lc_variant, multiplier, Box::new(hint_lc)));

                    // // println!("Hint = {:?}", hint);

                    // self.hints.push((current_lc_number, hint));

                    let (_new_var, hint_lc) = self.rewrite_lc(&c, one_fr, zero_fr);

                    let current_lc_number = self.increment_lc_number();

                    let hint = TranspilationVariant::<E>::MergeLinearCombinations((LcVariant::C, one_fr, Box::new(hint_lc)));

                    // println!("Hint = {:?}", hint);

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

                // println!("Hint = {:?}", hint);

                self.hints.push((current_lc_number, hint));

                return;

            },
            (true, true, false) => {
                let mut final_constant = a_constant_coeff;
                final_constant.mul_assign(&b_constant_coeff);

                let (_new_var, hint_lc) = self.rewrite_lc(&c, one_fr, final_constant);

                let current_lc_number = self.increment_lc_number();

                let hint = TranspilationVariant::<E>::MergeLinearCombinations((LcVariant::C, one_fr, Box::new(hint_lc)));

                // println!("Hint = {:?}", hint);

                self.hints.push((current_lc_number, hint));

            },
            (false, false, false) => {
                // potentially it can still be quadratic
                let (is_quadratic_gate, coeffs) = is_quadratic_gate::<E, Self>(&a, &b, &c, &mut self.scratch);
                if is_quadratic_gate {
                    let current_lc_number = self.increment_lc_number();

                    let hint = TranspilationVariant::<E>::IntoQuandaticGate(coeffs);

                    // println!("Hint = {:?}", hint);

                    self.hints.push((current_lc_number, hint));

                    return;
                }

                // rewrite into addition gates and multiplication gates
                
                let (_new_a_var, hint_a) = self.rewrite_lc(&a, one_fr, zero_fr);
                let (_new_b_var, hint_b) = self.rewrite_lc(&b, one_fr, zero_fr);
                let (_new_c_var, hint_c) = self.rewrite_lc(&c, one_fr, zero_fr);

                let current_lc_number = self.increment_lc_number();

                let hint = TranspilationVariant::<E>::TransformLc(Box::new((hint_a, hint_b, hint_c)));

                // println!("Hint = {:?}", hint);

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

    let is_quadratic;
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

fn get_first_variable<E: Engine, CS: ConstraintSystem<E>>(lc: &LinearCombination<E>) -> (bool, Variable) {
    let cs_one = CS::one();
    
    for (var, _) in lc.as_ref().iter() {
        if var != &cs_one {
            return (true, *var);
        }
    }

    (false, cs_one)
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

    // this linear combination has only 2 non-constant terms that 

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

fn deduplicate_stable<E: Engine, CS: ConstraintSystem<E>>(
    lc: LinearCombination<E>,
    scratch: &mut HashMap<crate::cs::Variable, usize>
) -> LinearCombination<E> {
    assert!(scratch.is_empty());

    if lc.as_ref().len() == 0 {
        return lc;
    }

    let mut deduped_vec: Vec<(crate::cs::Variable, E::Fr)> = Vec::with_capacity(lc.as_ref().len());

    for (var, coeff) in lc.0.into_iter() {
        if let Some(existing_index) = scratch.get(&var) {
            let (_, c) = &mut deduped_vec[*existing_index];
            c.add_assign(&coeff);
        } else {
            let new_idx = deduped_vec.len();
            deduped_vec.push((var, coeff));
            scratch.insert(var, new_idx);
        }
    }

    assert!(deduped_vec.len() != 0);

    scratch.clear();

    LinearCombination(deduped_vec)
}


pub struct Adaptor<'a, E: Engine, CS: PlonkConstraintSystem<E> + 'a> {
    cs: &'a mut CS,
    hints: &'a Vec<(usize, TranspilationVariant<E>)>,
    current_constraint_index: usize,
    current_hint_index: usize,
    scratch: HashSet<crate::cs::Variable>,
    // deduplication_scratch: HashMap<crate::cs::Variable, E::Fr>,
    deduplication_scratch: HashMap<crate::cs::Variable, usize>,
}

impl<'a, E: Engine, CS: PlonkConstraintSystem<E> + 'a> Adaptor<'a, E, CS> {
    // fn get_next_hint(&mut self) -> &(usize, TranspilationVariant<E>) {
    //     let current_hint_index = self.current_hint_index;
    //     let expected_constraint_index = self.current_constraint_index;

    //     let next_hint = &self.hints[current_hint_index];

    //     assert!(next_hint.0 == expected_constraint_index);

    //     self.current_hint_index += 1;
    //     self.current_constraint_index += 1;

    //     next_hint
    // }

    fn get_next_hint(&mut self) -> (usize, TranspilationVariant<E>) {
        let current_hint_index = self.current_hint_index;
        let expected_constraint_index = self.current_constraint_index;

        let next_hint = self.hints[current_hint_index].clone();

        assert!(next_hint.0 == expected_constraint_index);

        self.current_hint_index += 1;
        self.current_constraint_index += 1;

        next_hint
    }

    // make a new variable based on existing ones
    fn make_single_addition_gate(&mut self, lc: &LinearCombination<E>, gate_coeffs: (E::Fr, E::Fr, E::Fr, E::Fr)) -> Result<PlonkVariable, SynthesisError> {
        let zero_fr = E::Fr::zero();
        
        let mut minus_one_fr = E::Fr::one();
        minus_one_fr.negate();

        let (a_coeff, b_coeff, c_coeff, constant_coeff) = gate_coeffs;

        assert!(c_coeff == minus_one_fr);

        // we can just make an addition gate
        let cs_one = Self::one();

        let it = lc.as_ref().iter();

        if b_coeff.is_zero() {
            let mut a_var = PlonkVariable::new_unchecked(PlonkIndex::Aux(0));
            for (var, _) in it {
                if var == &cs_one {
                    continue
                } else {
                    a_var = convert_variable(*var);
                    break;
                }
            }

            let a_value = self.cs.get_value(a_var);

            let new_var = self.cs.alloc( 
            || {
                let mut c_value = a_value?;
                c_value.mul_assign(&a_coeff);
                c_value.add_assign(&constant_coeff);
                c_value.negate();

                Ok(c_value)
                // c = - constant - a*a_coeff
            })?;

            self.cs.new_gate((a_var, self.cs.get_dummy_variable(), new_var), (a_coeff, b_coeff, c_coeff, zero_fr, constant_coeff))?;

            Ok(new_var)
        } else {
            let mut a_var = PlonkVariable::new_unchecked(PlonkIndex::Aux(0));
            let mut b_var = PlonkVariable::new_unchecked(PlonkIndex::Aux(0));
            let mut found_a = false;

            for (var, _) in it {
                if var == &cs_one {
                    continue
                } else {
                    if !found_a {
                        found_a = true;
                        a_var = convert_variable(*var);
                    } else {
                        b_var = convert_variable(*var);
                        break;
                    }
                }
            }

            let a_value = self.cs.get_value(a_var);
            let b_value = self.cs.get_value(b_var);

            let new_var = self.cs.alloc( 
                || {
                    let a_value = a_value?;
                    let mut b_value = b_value?;
                    b_value.mul_assign(&b_coeff);
                    let mut c_value = a_value;
                    c_value.mul_assign(&a_coeff);
                    c_value.add_assign(&b_value);
                    c_value.add_assign(&constant_coeff);
                    c_value.negate();
    
                    Ok(c_value)
                    // c = - constant - a*a_coeff - b*b_coeff
                })?;

            self.cs.new_gate((a_var, b_var, new_var), (a_coeff, b_coeff, c_coeff, zero_fr, constant_coeff))?;

            Ok(new_var)
        }
    }

    // make a new variable based on existing ones
    fn make_chain_of_addition_gates(&mut self, lc: &LinearCombination<E>, first_gate_coeffs: (E::Fr, E::Fr, E::Fr, E::Fr), chain_coeffs: Vec<E::Fr>) -> Result<PlonkVariable, SynthesisError> {
        let zero_fr = E::Fr::zero();
        let one_fr = E::Fr::one();
        
        let mut minus_one_fr = E::Fr::one();
        minus_one_fr.negate();

        let (a_coeff, b_coeff, c_coeff, constant_coeff) = first_gate_coeffs;

        assert!(c_coeff == minus_one_fr);
        assert!(!b_coeff.is_zero());

        // we can just make an addition gate
        let cs_one = Self::one();

        let mut it = lc.as_ref().iter();

        let mut new_var = if b_coeff.is_zero() {
            unreachable!()

            // let mut a_var = PlonkVariable::new_unchecked(PlonkIndex::Aux(0));
            // for (var, _) in &mut it {
            //     if var == &cs_one {
            //         continue
            //     } else {
            //         a_var = convert_variable(*var);
            //         break;
            //     }
            // }

            // let a_value = self.cs.get_value(a_var);

            // let new_var = self.cs.alloc( 
            // || {
            //     let mut c_value = a_value?;
            //     c_value.mul_assign(&a_coeff);
            //     c_value.add_assign(&constant_coeff);
            //     c_value.negate();

            //     Ok(c_value)
            //     // c = - constant - a*a_coeff
            // })?;

            // new_var
        } else {
            let mut a_var = PlonkVariable::new_unchecked(PlonkIndex::Aux(0));
            let mut b_var = PlonkVariable::new_unchecked(PlonkIndex::Aux(0));
            let mut found_a = false;

            for (var, _) in &mut it {
                if var == &cs_one {
                    continue
                } else {
                    if !found_a {
                        found_a = true;
                        a_var = convert_variable(*var);
                    } else {
                        b_var = convert_variable(*var);
                        break;
                    }
                }
            }

            let a_value = self.cs.get_value(a_var);
            let b_value = self.cs.get_value(b_var);

            let new_var = self.cs.alloc( 
                || {
                    let a_value = a_value?;
                    let mut b_value = b_value?;
                    b_value.mul_assign(&b_coeff);
                    let mut c_value = a_value;
                    c_value.mul_assign(&a_coeff);
                    c_value.add_assign(&b_value);
                    c_value.add_assign(&constant_coeff);
                    c_value.negate();
    
                    Ok(c_value)
                    // c = - constant - a*a_coeff - b*b_coeff
                })?;

            self.cs.new_gate((a_var, b_var, new_var), (a_coeff, b_coeff, c_coeff, zero_fr, constant_coeff))?;

            new_var
        };

        // next gates are 1*old_new_var + b*original_var - new_new_var = 0

        let mut chain_iter = chain_coeffs.into_iter();

        for ((var, _), hint_coeff) in (&mut it).zip(&mut chain_iter) {
            if var != &cs_one {
                let original_var = convert_variable(*var);
                let original_var_value = self.cs.get_value(original_var);
                let new_var_value = self.cs.get_value(new_var);

                let old_new_var = new_var;

                new_var = self.cs.alloc( 
                    || {
                        let mut new = original_var_value?;
                        new.mul_assign(&hint_coeff);
                        new.add_assign(&new_var_value?);

                        Ok(new)
                    })?;

                self.cs.new_gate((old_new_var, original_var, new_var), (one_fr, hint_coeff, minus_one_fr, zero_fr, zero_fr))?;
            }
        }

        assert!(chain_iter.next().is_none());

        Ok(new_var)
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

impl<'a, E: Engine, CS: PlonkConstraintSystem<E> + 'a> crate::ConstraintSystem<E>
    for Adaptor<'a, E, CS>
{
    type Root = Self;

    fn one() -> crate::Variable {
        crate::Variable::new_unchecked(crate::Index::Input(0))
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
            PlonkVariable(PlonkIndex::Aux(index)) => crate::Variable::new_unchecked(crate::Index::Aux(index)),
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
            PlonkVariable(PlonkIndex::Input(index)) => crate::Variable::new_unchecked(crate::Index::Input(index)),
            _ => unreachable!(),
        })
    }

    fn enforce<A, AR, LA, LB, LC>(&mut self, _ann: A, a: LA, b: LB, c: LC)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
        LA: FnOnce(crate::LinearCombination<E>) -> crate::LinearCombination<E>,
        LB: FnOnce(crate::LinearCombination<E>) -> crate::LinearCombination<E>,
        LC: FnOnce(crate::LinearCombination<E>) -> crate::LinearCombination<E>,
    {
        // let ann: String = _ann().into();
        // println!("Enforce {}", ann);

        let zero_fr = E::Fr::zero();
        let one_fr = E::Fr::one();
        let mut minus_one_fr = E::Fr::one();
        minus_one_fr.negate();

        let (_, hint) = { 
            self.get_next_hint() 
        };

        let a = { deduplicate_stable::<E, Self>(a(crate::LinearCombination::zero()), &mut self.deduplication_scratch) };
        let b = { deduplicate_stable::<E, Self>(b(crate::LinearCombination::zero()), &mut self.deduplication_scratch) };
        let c = { deduplicate_stable::<E, Self>(c(crate::LinearCombination::zero()), &mut self.deduplication_scratch) };

        let (a_is_constant, _a_constant_coeff) = is_constant::<E, Self>(&a);
        let (b_is_constant, _b_constant_coeff) = is_constant::<E, Self>(&b);
        let (c_is_constant, _c_constant_coeff) = is_constant::<E, Self>(&c); 

        let (a_has_variable, a_first_variable) = get_first_variable::<E, Self>(&a);
        let (b_has_variable, b_first_variable) = get_first_variable::<E, Self>(&b);
        let (c_has_variable, c_first_variable) = get_first_variable::<E, Self>(&c);

        debug_assert!(a_is_constant & a_has_variable == false);
        debug_assert!(b_is_constant & b_has_variable == false);
        debug_assert!(c_is_constant & c_has_variable == false);

        let dummy_var = self.cs.get_dummy_variable();

        // variables are left, right, output
        // coefficients are left, right, output, multiplication, constant

        match hint {
            TranspilationVariant::IntoLinearGate((c0, c1)) => {
                let var = if c_has_variable {
                    convert_variable(c_first_variable)
                } else if b_has_variable {
                    convert_variable(b_first_variable)
                } else if a_has_variable {
                    convert_variable(a_first_variable)
                } else {
                    unreachable!();
                };

                self.cs.new_gate((var, dummy_var, dummy_var), (c1, zero_fr, zero_fr, zero_fr, c0)).expect("must make a gate");

            },
            TranspilationVariant::IntoQuandaticGate((c0, c1, c2)) => {
                let var = if c_has_variable {
                    convert_variable(c_first_variable)
                } else if b_has_variable {
                    convert_variable(b_first_variable)
                } else if a_has_variable {
                    convert_variable(a_first_variable)
                } else {
                    unreachable!();
                };

                self.cs.new_gate((var, var, dummy_var), (c1, zero_fr, zero_fr, c2, c0)).expect("must make a gate");
            },
            TranspilationVariant::TransformLc(boxed_hints) => {
                let (t_a, t_b, t_c) = *boxed_hints;
                let mut multiplication_constant = one_fr;
                let a_var = match t_a {
                    TranspilationVariant::IntoSingleAdditionGate(coeffs) => {
                        self.make_single_addition_gate(&a, coeffs).expect("must make a gate")
                    },
                    TranspilationVariant::IntoMultipleAdditionGates(coeffs, chain) => {
                        self.make_chain_of_addition_gates(&a, coeffs, chain).expect("must make a gate")
                    },
                    TranspilationVariant::LeaveAsSingleVariable(coeff) => {
                        assert!(a_has_variable);
                        multiplication_constant.mul_assign(&coeff);

                        convert_variable(a_first_variable)
                    },
                    _ => {unreachable!("{:?}", t_a)}
                };

                let b_var = match t_b {
                    TranspilationVariant::IntoSingleAdditionGate(coeffs) => {
                        self.make_single_addition_gate(&b, coeffs).expect("must make a gate")
                    },
                    TranspilationVariant::IntoMultipleAdditionGates(coeffs, chain) => {
                        self.make_chain_of_addition_gates(&b, coeffs, chain).expect("must make a gate")
                    },
                    TranspilationVariant::LeaveAsSingleVariable(coeff) => {
                        assert!(b_has_variable);
                        multiplication_constant.mul_assign(&coeff);

                        convert_variable(b_first_variable)
                    },
                    _ => {unreachable!("{:?}", t_b)}
                };

                let (c_is_just_a_constant, c_var) = match t_c {
                    TranspilationVariant::IntoSingleAdditionGate(coeffs) => {
                        (false, Some(self.make_single_addition_gate(&c, coeffs).expect("must make a gate")) )
                    },
                    TranspilationVariant::IntoMultipleAdditionGates(coeffs, chain) => {
                        (false, Some(self.make_chain_of_addition_gates(&c, coeffs, chain).expect("must make a gate")) )
                    },
                    TranspilationVariant::LeaveAsSingleVariable(coeff) => {
                        assert!(c_has_variable);
                        multiplication_constant.mul_assign(&coeff);

                        (false, Some(convert_variable(c_first_variable)) )
                    },
                    TranspilationVariant::IsConstant(value) => {
                        assert!(c_is_constant);
                        assert!(_c_constant_coeff == value);
                        (true, None)
                    }
                    _ => {unreachable!("{:?}", t_c)}
                };

                if c_is_just_a_constant {
                    let mut constant_term = _c_constant_coeff;
                    constant_term.negate();

                    // A*B == constant
                    self.cs.new_gate((a_var, b_var, dummy_var), (zero_fr, zero_fr, zero_fr, multiplication_constant, constant_term)).expect("must make a gate");
                } else {
                    let c_var = c_var.expect("must be a variable");
                    self.cs.new_gate((a_var, b_var, c_var), (zero_fr, zero_fr, minus_one_fr, multiplication_constant, zero_fr)).expect("must make a gate");
                }
            },
            TranspilationVariant::IntoMultipleAdditionGates(_, _) => {
                unreachable!()
            },
            TranspilationVariant::IntoSingleAdditionGate(_) => {
                unreachable!()
            },
            TranspilationVariant::IsConstant(_) => {
                unreachable!()
            },
            TranspilationVariant::LeaveAsSingleVariable(_) => {
                unreachable!()
            },
            TranspilationVariant::MergeLinearCombinations(_) => {
                unreachable!()
            }
        }
        // self.cs.new_gate((a_var, b_var, c_var), (a_coef, x, y, z, c_1));    
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

fn convert_variable(r1cs_variable: crate::Variable) -> PlonkVariable {
    let var = match r1cs_variable.get_unchecked() {
        crate::Index::Input(0) => {unreachable!()},
        crate::Index::Aux(0) => {unreachable!()},
        crate::Index::Input(i) => PlonkVariable(PlonkIndex::Input(i)),
        crate::Index::Aux(i) => PlonkVariable(PlonkIndex::Aux(i)),
    };

    var
}

use std::cell::Cell;

pub struct AdaptorCircuit<'a, E:Engine, C: crate::Circuit<E>>{
    circuit: Cell<Option<C>>,
    hints: &'a Vec<(usize, TranspilationVariant<E>)>,
}

impl<'a, E:Engine, C: crate::Circuit<E>> AdaptorCircuit<'a, E, C> {
    pub fn new<'b>(circuit: C, hints: &'b Vec<(usize, TranspilationVariant<E>)>) -> Self 
        where 'b: 'a 
    {
        Self {
            circuit: Cell::new(Some(circuit)),
            hints: hints
        }
    }
}

impl<'a, E: Engine, C: crate::Circuit<E>> PlonkCircuit<E> for AdaptorCircuit<'a, E, C> {
    fn synthesize<CS: PlonkConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        let mut adaptor = Adaptor {
            cs: cs,
            hints: self.hints,
            current_constraint_index: 0,
            current_hint_index: 0,
            scratch: HashSet::with_capacity((E::Fr::NUM_BITS * 2) as usize),
            deduplication_scratch: HashMap::with_capacity((E::Fr::NUM_BITS * 2) as usize),
        };

        let c = self.circuit.replace(None).unwrap();

        match c.synthesize(&mut adaptor) {
            Err(_) => return Err(SynthesisError::AssignmentMissing),
            Ok(_) => {}
        };

        Ok(())
    }
}

#[test]
fn transpile_xor_using_adaptor() {
    use crate::tests::XORDemo;
    use crate::cs::Circuit;
    use crate::pairing::bn256::Bn256;
    use crate::plonk::plonk::generator::*;

    let c = XORDemo::<Bn256> {
        a: None,
        b: None,
        _marker: PhantomData
    };

    let mut transpiler = Transpiler::new();

    c.synthesize(&mut transpiler).unwrap();

    let hints = transpiler.hints;

    let c = XORDemo::<Bn256> {
        a: None,
        b: None,
        _marker: PhantomData
    };

    let adapted_curcuit = AdaptorCircuit::new(c, &hints);

    let mut assembly = GeneratorAssembly::<Bn256>::new();
    adapted_curcuit.synthesize(&mut assembly).unwrap();
    assembly.finalize();

    for (i, g) in assembly.aux_gates.iter().enumerate() {
        println!("Gate {} = {:?}", i, g);
    }
}