use crate::pairing::ff::{Field, PrimeField};
use crate::pairing::{Engine};

use crate::SynthesisError;

use super::test_assembly::Gate;
use crate::plonk::cs::gates::Variable as PlonkVariable;
use crate::plonk::cs::gates::Index as PlonkIndex;

use super::cs::Circuit as PlonkCircuit;
use super::cs::ConstraintSystem as PlonkConstraintSystem;

use std::marker::PhantomData;

use std::collections::{HashSet, HashMap};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MergeLcVariant {
    AIsTheOnlyMeaningful,
    BIsTheOnlyMeaningful,
    MergeABWithConstantC,
    MergeACThroughConstantB,
    MergeBCThroughConstantA,
    CIsTheOnlyMeaningful,
}

// These are transpilation options over A * B - C = 0 constraint
#[derive(Clone, PartialEq, Eq)]
pub enum TranspilationVariant {
    LeaveAsSingleVariable,
    IntoQuadraticGate,
    IntoSingleAdditionGate,
    IntoMultipleAdditionGates,
    MergeLinearCombinations(MergeLcVariant, Box<TranspilationVariant>),
    IsConstant, 
    IntoMultiplicationGate(Box<(TranspilationVariant, TranspilationVariant, TranspilationVariant)>)
}

impl std::fmt::Debug for TranspilationVariant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TranspilationVariant::LeaveAsSingleVariable => {
                writeln!(f, "Variant: leave LC as a single variable")?;
            },
            TranspilationVariant::IntoQuadraticGate => {
                writeln!(f, "Variant: into quadratic gate")?;
            },
            TranspilationVariant::IntoSingleAdditionGate => {
                writeln!(f, "Variant: into single addition gate")?;
            },
            TranspilationVariant::IntoMultipleAdditionGates => {
                writeln!(f, "Variant: into multiple addition gates")?;
            },
            TranspilationVariant::MergeLinearCombinations(merge_type, _) => {
                writeln!(f, "Variant: merge linear combinations as {:?}", merge_type)?;
            },
            TranspilationVariant::IsConstant => {
                writeln!(f, "Variant: into constant factor")?;
            },
            TranspilationVariant::IntoMultiplicationGate(b) => {
                writeln!(f, "Variant: into combinatoric multiplication gate")?;
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
    hints: Vec<(usize, TranspilationVariant)>,
    _marker: std::marker::PhantomData<E>
}

fn allocate_single_linear_combination<E: Engine, CS: PlonkConstraintSystem<E, GateCoefficients = [E::Fr; 6]>> (
    cs: &mut CS,
    needs_next_step: bool,
    variables: (PlonkVariable, PlonkVariable, PlonkVariable),
    next_step_variable: Option<Variable>,
    coefficients: [E::Fr; 6]
) -> Result<Option<Variable>, SynthesisError> {
    if needs_next_step {
        assert!(next_step_variable.is_some());
    } else {
        assert!(next_step_variable.is_none());
        assert!(coefficients[5].is_zero());
    }

    cs.new_gate(variables, coefficients)?;

    Ok(next_step_variable)
}

fn evaluate_lc<E: Engine, CS: PlonkConstraintSystem<E>>(
    cs: &CS,
    lc: &LinearCombination<E>,  
    // multiplier: E::Fr, 
    free_term_constant: E::Fr
) -> Result<E::Fr, SynthesisError> {
    let mut final_value = E::Fr::zero();
    for (var, coeff) in lc.as_ref().iter() {
        let mut may_be_value = cs.get_value(convert_variable(*var))?;
        may_be_value.mul_assign(&coeff);
        final_value.add_assign(&may_be_value);
    }

    final_value.add_assign(&free_term_constant);

    Ok(final_value)
}

fn evaluate_over_variables<E: Engine, CS: PlonkConstraintSystem<E>>(
    cs: &CS,
    variables: &[(Variable, E::Fr)],
    // multiplier: E::Fr, 
    free_term_constant: E::Fr
) -> Result<E::Fr, SynthesisError> {
    let mut final_value = E::Fr::zero();
    for (var, coeff) in variables.iter() {
        let mut may_be_value = cs.get_value(convert_variable(*var))?;
        may_be_value.mul_assign(&coeff);
        final_value.add_assign(&may_be_value);
    }

    final_value.add_assign(&free_term_constant);

    Ok(final_value)
}

fn evaluate_over_plonk_variables<E: Engine, CS: PlonkConstraintSystem<E>>(
    cs: &CS,
    variables: &[(PlonkVariable, E::Fr)],
    // multiplier: E::Fr, 
    free_term_constant: E::Fr
) -> Result<E::Fr, SynthesisError> {
    let mut final_value = E::Fr::zero();
    for (var, coeff) in variables.iter() {
        let mut may_be_value = cs.get_value(*var)?;
        may_be_value.mul_assign(&coeff);
        final_value.add_assign(&may_be_value);
    }

    // if multiplier != E::Fr::one() {
    //     final_value.mul_assign(&multiplier);
    // }

    final_value.sub_assign(&free_term_constant);

    Ok(final_value)
}

fn enforce_lc_as_gates<E: Engine, CS: PlonkConstraintSystem<E, GateCoefficients = [E::Fr; 6]>>(
    cs: &mut CS, 
    mut lc: LinearCombination<E>,  
    multiplier: E::Fr, 
    free_term_constant: E::Fr,
    collapse_into_single_variable: bool
) -> (Option<PlonkVariable>, E::Fr, TranspilationVariant) {
    let zero_fr = E::Fr::zero();
    let one_fr = E::Fr::one();
    let mut minus_one_fr = E::Fr::one();
    minus_one_fr.negate();

    // trivial case - single variable

    assert!(lc.0.len() > 0);

    if lc.0.len() == 1 {
        if free_term_constant.is_zero() {
            if collapse_into_single_variable {
                // we try to make a multiplication gate
                let (var, coeff) = lc.0[0];

                return (Some(convert_variable(var)), coeff, TranspilationVariant::LeaveAsSingleVariable);
            }
        } 
    }

    // everything else should be handled here by making a new variable

    // scale if necessary
    if multiplier.is_zero() {
        assert!(free_term_constant.is_zero());
        unreachable!();
        // it's a constraint 0 * LC = 0
    } else {
        if multiplier != one_fr {
            for (_, c) in lc.0.iter_mut() {
                c.mul_assign(&multiplier);
            }
        }
    }

    let final_variable = if collapse_into_single_variable {
        let may_be_new_value = evaluate_lc::<E, CS>(&*cs, &lc, free_term_constant);
        let new_var = cs.alloc(|| {
            may_be_new_value
        }).expect("must allocate a new variable to collapse LC");

        Some(new_var)
    } else {
        None
    };

    if let Some(var) = final_variable {
        subtract_variable_unchecked(&mut lc, convert_variable_back(var));
    }

    let num_terms = lc.0.len();

    // we have two options: 
    // - fit everything into a single gate (in case of 3 terms in the linear combination)
    // - make a required number of extra variables and chain it
    
    if num_terms <= 3 {
        // we can just make a single gate

        let mut found_a = false;
        let mut found_b = false;

        let mut a_var = cs.get_dummy_variable();
        let mut b_var = cs.get_dummy_variable();
        let mut c_var = cs.get_dummy_variable();

        let mut a_coeff = E::Fr::zero();
        let mut b_coeff = E::Fr::zero();
        let mut c_coeff = E::Fr::zero();

        let it = lc.0.into_iter();

        for (var, coeff) in it {
            if !found_a {
                found_a = true;
                a_coeff = coeff;
                a_var = convert_variable(var);
            } else if !found_b {
                found_b = true;
                b_coeff = coeff;
                b_var = convert_variable(var);
            } else {
                c_coeff = coeff;
                c_var = convert_variable(var);
            }
        }

        // if multiplier == E::Fr::zero() {
        //     assert!(free_term_constant == E::Fr::zero());
        //     unreachable!();
        //     // it's a constraint 0 * LC = 0
        // } else {
        //     //scale
        //     if multiplier != one_fr {
        //         a_coeff.mul_assign(&multiplier);
        //         a_coeff.mul_assign(&multiplier);
        //         a_coeff.mul_assign(&multiplier);
        //     }
        // }

        // free_term_constant.negate();


        cs.new_gate((a_var, b_var, c_var), [a_coeff, b_coeff, c_coeff, zero_fr, free_term_constant, zero_fr]).expect("must make a gate to form an LC");

        let hint = TranspilationVariant::IntoSingleAdditionGate;

        return (final_variable, one_fr, hint);
    } else {
        // we can take:
        // - 3 variables to form the first gate and place their sum into the C wire of the next gate
        // - every time take 2 variables and place their sum + C wire into the next gate C wire

        // we have also made a final variable already, so there is NO difference
        let cycles = ((lc.0.len() - 3) + 1) / 2; // ceil 
        let mut it = lc.0.into_iter();

        let mut c_var = {
            let (v0, c0) = it.next().expect("there must be a term");
            let (v1, c1) = it.next().expect("there must be a term");
            let (v2, c2) = it.next().expect("there must be a term");

            let may_be_new_intermediate_value = evaluate_over_variables::<E, CS>(&*cs, &[(v0, c0), (v1, c1), (v2, c2)], free_term_constant);
            let new_intermediate_var = cs.alloc(|| {
                may_be_new_intermediate_value
            }).expect("must allocate a new intermediate variable to collapse LC");

            let a_var = convert_variable(v0);
            let b_var = convert_variable(v1);
            let c_var = convert_variable(v2);

            cs.new_gate((a_var, b_var, c_var), [c0, c1, c2, zero_fr, free_term_constant, minus_one_fr]).expect("must make a gate to form an LC");

            new_intermediate_var
        };

        for _ in 0..(cycles-1) {
            let mut found_a = false;
            let mut a_coeff = E::Fr::zero();
            let mut b_coeff = E::Fr::zero();

            let mut a_var = cs.get_dummy_variable();
            let mut b_var = cs.get_dummy_variable();

            for (var, coeff) in &mut it {
                if !found_a {
                    found_a = true;
                    a_coeff = coeff;
                    a_var = convert_variable(var);
                } else {
                    b_coeff = coeff;
                    b_var = convert_variable(var);
                    break;
                }
            }

            let may_be_new_intermediate_value = evaluate_over_plonk_variables::<E, CS>(
                &*cs, 
                &[(a_var, a_coeff), (b_var, b_coeff), (c_var, one_fr)], 
                zero_fr
            );

            let new_intermediate_var = cs.alloc(|| {
                may_be_new_intermediate_value
            }).expect("must allocate a new intermediate variable to collapse LC");

            cs.new_gate(
                (a_var, b_var, c_var), 
                [a_coeff, b_coeff, one_fr, zero_fr, zero_fr, minus_one_fr]
            ).expect("must make a gate to form an LC");

            c_var = new_intermediate_var
        }

        // final step - don't just to the next gate
        {
            let mut found_a = false;
            let mut a_coeff = E::Fr::zero();
            let mut b_coeff = E::Fr::zero();

            let mut a_var = cs.get_dummy_variable();
            let mut b_var = cs.get_dummy_variable();

            for (var, coeff) in &mut it {
                if !found_a {
                    found_a = true;
                    a_coeff = coeff;
                    a_var = convert_variable(var);
                } else {
                    b_coeff = coeff;
                    b_var = convert_variable(var);
                    break;
                }
            }

            cs.new_gate(
                (a_var, b_var, c_var), 
                [a_coeff, b_coeff, one_fr, zero_fr, zero_fr, zero_fr]
            ).expect("must make a final gate to form an LC");
        }

        assert!(it.next().is_none());

        let hint = TranspilationVariant::IntoMultipleAdditionGates;

        return (final_variable, one_fr, hint);   
    }
}

impl<E: Engine> Transpiler<E> {
    pub fn new() -> Self {
        Self {
            current_constraint_index: 0,
            current_plonk_input_idx: 0,
            current_plonk_aux_idx: 0,
            scratch: HashSet::with_capacity((E::Fr::NUM_BITS * 2) as usize),
            deduplication_scratch: HashMap::with_capacity((E::Fr::NUM_BITS * 2) as usize),
            hints: vec![],
            _marker: std::marker::PhantomData
        }
    }

    pub fn into_hints(self) -> Vec<(usize, TranspilationVariant)> {
        self.hints
    }

    fn increment_lc_number(&mut self) -> usize {
        let current_lc_number = self.current_constraint_index;
        self.current_constraint_index += 1;

        current_lc_number
    }
}

impl<E: Engine> PlonkConstraintSystem<E> for Transpiler<E> {
    type GateCoefficients = [E::Fr; 6];

    fn alloc<F>(&mut self, value: F) -> Result<PlonkVariable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError> 
    {
        let var = crate::ConstraintSystem::<E>::alloc(
            self,
            || "alloc aux var", 
        value)?;

        Ok(convert_variable(var))
    }

    // allocate an input variable
    fn alloc_input<F>(&mut self, value: F) -> Result<PlonkVariable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError> 
    {
        let var = crate::ConstraintSystem::<E>::alloc_input(
            self,
            || "alloc input var", 
        value)?;
        Ok(convert_variable(var))
    }

    fn new_gate(&mut self, 
        _variables: (PlonkVariable, PlonkVariable, PlonkVariable), 
        _coeffs: Self::GateCoefficients
    ) -> Result<(), SynthesisError> 
    {
        Ok(())
    }

    fn get_dummy_variable(&self) -> PlonkVariable {
        PlonkVariable::new_unchecked(PlonkIndex::Aux(0))
    }
}

impl<'a, E: Engine> PlonkConstraintSystem<E> for &'a mut Transpiler<E> {
    type GateCoefficients = [E::Fr; 6];

    fn alloc<F>(&mut self, value: F) -> Result<PlonkVariable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError> 
    {
        let var = crate::ConstraintSystem::<E>::alloc(
            self,
            || "alloc aux var", 
        value)?;

        Ok(convert_variable(var))
    }

    // allocate an input variable
    fn alloc_input<F>(&mut self, value: F) -> Result<PlonkVariable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError> 
    {
        let var = crate::ConstraintSystem::<E>::alloc_input(
            self,
            || "alloc input var", 
        value)?;
        Ok(convert_variable(var))
    }

    fn new_gate(&mut self, 
        _variables: (PlonkVariable, PlonkVariable, PlonkVariable), 
        _coeffs: Self::GateCoefficients
    ) -> Result<(), SynthesisError> 
    {
        Ok(())
    }

    fn get_dummy_variable(&self) -> PlonkVariable {
        PlonkVariable::new_unchecked(PlonkIndex::Aux(0))
    }
}

impl<E: Engine> crate::ConstraintSystem<E> for Transpiler<E>
{
    type Root = Self;

    fn one() -> crate::Variable {
        crate::Variable::new_unchecked(crate::Index::Input(0))
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
        // if ann.contains("y-coordinate lookup") {
        //     // 
        //     let _t = E::Fr::one();
        // };
        // println!("Enforce {}", ann);

        let zero_fr = E::Fr::zero();
        let one_fr = E::Fr::one();

        let mut negative_one_fr = E::Fr::one();
        negative_one_fr.negate();

        // we need to determine the type of transformation constraint

        // let's handle trivial cases first

        // A or B or C are just constant terms

        let (a_has_constant, a_constant_term, a_lc_is_empty, a_lc) = deduplicate_and_split_linear_term::<E, Self>(a(crate::LinearCombination::zero()), &mut self.deduplication_scratch);
        let (b_has_constant, b_constant_term, b_lc_is_empty, b_lc) = deduplicate_and_split_linear_term::<E, Self>(b(crate::LinearCombination::zero()), &mut self.deduplication_scratch);
        let (c_has_constant, c_constant_term, c_lc_is_empty, c_lc) = deduplicate_and_split_linear_term::<E, Self>(c(crate::LinearCombination::zero()), &mut self.deduplication_scratch);

        let a_is_constant = a_has_constant & a_lc_is_empty;
        let b_is_constant = b_has_constant & b_lc_is_empty;
        let c_is_constant = c_has_constant & c_lc_is_empty;

        // debug_assert!(a_has_constant || !a_lc_is_empty);
        // debug_assert!(b_has_constant || !b_lc_is_empty);
        // debug_assert!(c_has_constant || !c_lc_is_empty);

        match (a_is_constant, b_is_constant, c_is_constant) {
            (true, true, true) => {
                unreachable!("R1CS has a gate 1 * 1 = 1");
            },
            (true, false, true) | (false, true, true) => {
                // println!("C * LC = C");
                // we have something like c0 * LC = c1
                let lc = if !a_is_constant {
                    a_lc
                } else if !b_is_constant {
                    b_lc
                } else {
                    unreachable!("Either A or B LCs are constant");
                };

                let multiplier = if a_is_constant {
                    a_constant_term
                } else if b_is_constant {
                    b_constant_term
                } else {
                    unreachable!("Must take multiplier from A or B");
                };

                let mut free_constant_term = if a_is_constant {
                    b_constant_term
                } else if b_is_constant {
                    a_constant_term
                } else {
                    unreachable!("Either A or B LCs are constant");
                };

                free_constant_term.mul_assign(&multiplier);
                free_constant_term.sub_assign(&c_constant_term);

                let (_, _, hint) = enforce_lc_as_gates(
                    self,
                    lc,
                    multiplier,
                    free_constant_term,
                    false,
                );

                let current_lc_number = self.increment_lc_number();

                // println!("Hint = {:?}", hint);

                self.hints.push((current_lc_number, hint));

            },
            (false, false, true) => {
                // println!("LC * LC = C");    
                // potential quadatic gate
                let (is_quadratic_gate, _coeffs) = check_for_quadratic_gate::<E>(
                    &a_lc, 
                    &b_lc, 
                    &c_lc,
                    a_constant_term,
                    b_constant_term,
                    c_constant_term
                );
                if is_quadratic_gate {
                    let current_lc_number = self.increment_lc_number();

                    let hint = TranspilationVariant::IntoQuadraticGate;

                    // println!("Hint = {:?}", hint);

                    self.hints.push((current_lc_number, hint));

                    return;
                }

                let (_new_a_var, _, hint_a) = enforce_lc_as_gates(
                    self,
                    a_lc,
                    one_fr,
                    a_constant_term,
                    true,
                );

                let (_new_b_var, _, hint_b) = enforce_lc_as_gates(
                    self,
                    b_lc,
                    one_fr,
                    b_constant_term,
                    true,
                );

                let current_lc_number = self.increment_lc_number();

                let hint_c = TranspilationVariant::IsConstant;

                let hint = TranspilationVariant::IntoMultiplicationGate(Box::new((hint_a, hint_b, hint_c)));

                // println!("Hint = {:?}", hint);

                self.hints.push((current_lc_number, hint));

            },
            (true, false, false) | (false, true, false) => {
                // LC * 1 = LC
                // println!("C * LC = LC");
                let multiplier = if a_is_constant {
                    a_constant_term
                } else if b_is_constant {
                    b_constant_term
                } else {
                    unreachable!()
                };

                let lc_variant = if a_is_constant {
                    MergeLcVariant::MergeBCThroughConstantA
                } else {
                    MergeLcVariant::MergeACThroughConstantB
                };

                if multiplier == zero_fr {
                    // LC_AB * 0 = LC_C => LC_C == 0

                    let (_, _, hint_c) = enforce_lc_as_gates(
                        self,
                        c_lc,
                        one_fr,
                        zero_fr,
                        false,
                    );

                    let current_lc_number = self.increment_lc_number();

                    let hint = TranspilationVariant::MergeLinearCombinations(MergeLcVariant::CIsTheOnlyMeaningful, Box::new(hint_c));

                    // println!("Hint = {:?}", hint);

                    self.hints.push((current_lc_number, hint));

                    return;
                }

                let mut final_lc = if !a_is_constant {
                    a_lc
                } else if !b_is_constant {
                    b_lc
                } else {
                    unreachable!()
                };

                if multiplier != one_fr {
                    for (_, c) in final_lc.0.iter_mut() {
                        c.mul_assign(&multiplier);
                    }
                }

                let mut free_constant_term = a_constant_term;
                free_constant_term.mul_assign(&multiplier);
                free_constant_term.sub_assign(&c_constant_term);

                // let final_lc = final_lc - &c;
                let final_lc = subtract_lcs_with_dedup_stable::<E, Self>(final_lc, c_lc, &mut self.deduplication_scratch);

                let (_, _, hint_lc) = enforce_lc_as_gates(
                    self,
                    final_lc,
                    one_fr,
                    free_constant_term,
                    false,
                );

                let current_lc_number = self.increment_lc_number();

                let hint = TranspilationVariant::MergeLinearCombinations(lc_variant, Box::new(hint_lc));

                // println!("Hint = {:?}", hint);

                self.hints.push((current_lc_number, hint));

                return;

            },
            (true, true, false) => {
                // println!("C * C = LC");
                // A and B are some constants
                let mut free_constant_term = a_constant_term;
                free_constant_term.mul_assign(&b_constant_term);

                let (_, _, hint_lc) = enforce_lc_as_gates(
                    self,
                    c_lc,
                    one_fr,
                    free_constant_term,
                    false,
                );

                let current_lc_number = self.increment_lc_number();

                let hint = TranspilationVariant::MergeLinearCombinations(MergeLcVariant::CIsTheOnlyMeaningful, Box::new(hint_lc));

                // println!("Hint = {:?}", hint);

                self.hints.push((current_lc_number, hint));

            },
            (false, false, false) => {
                // println!("LC * LC = LC");
                // potentially it can still be quadratic
                let (is_quadratic_gate, _coeffs) = is_quadratic_gate::<E, Self>(
                    &a_lc, 
                    &b_lc, 
                    &c_lc, &mut self.scratch);
                if is_quadratic_gate {
                    let current_lc_number = self.increment_lc_number();

                    let hint = TranspilationVariant::IntoQuadraticGate;

                    // println!("Hint = {:?}", hint);

                    self.hints.push((current_lc_number, hint));

                    return;
                }

                // rewrite into addition gates and multiplication gates
                
                let (_new_a_var, _, hint_a) = enforce_lc_as_gates(
                    self,
                    a_lc,
                    one_fr,
                    a_constant_term,
                    true,
                );
                let (_new_b_var, _, hint_b) = enforce_lc_as_gates(
                    self,
                    b_lc,
                    one_fr,
                    b_constant_term,
                    true,
                );
                let (_new_c_var, _, hint_c) = enforce_lc_as_gates(
                    self,
                    c_lc,
                    one_fr,
                    c_constant_term,
                    true,
                );

                let current_lc_number = self.increment_lc_number();

                let hint = TranspilationVariant::IntoMultiplicationGate(Box::new((hint_a, hint_b, hint_c)));

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

fn check_for_quadratic_gate<E: Engine>(
    a: &LinearCombination<E>, 
    b: &LinearCombination<E>, 
    c: &LinearCombination<E>,
    a_constant_term: E::Fr,
    b_constant_term: E::Fr,
    c_constant_term: E::Fr,
) -> (bool, (E::Fr, E::Fr, E::Fr)) {
    let zero = E::Fr::zero();

    let a_is_linear = a.0.len() == 1;
    let b_is_linear = b.0.len() == 1;
    let c_is_linear = c.0.len() == 1;

    let c_is_empty = c.0.len() == 0;

    let mut a_linear_var_coeff = E::Fr::zero();
    let mut b_linear_var_coeff = E::Fr::zero();
    let mut c_linear_var_coeff = E::Fr::zero();

    let mut is_quadratic = false;
    if c_is_empty {
        if a_is_linear && b_is_linear {
            let (a_linear_var, a_coeff) = a.0[0];
            let (b_linear_var, b_coeff) = b.0[0];
            a_linear_var_coeff = a_coeff;
            b_linear_var_coeff = b_coeff;

            is_quadratic = a_linear_var == b_linear_var;
        }
    } else {
        if a_is_linear && b_is_linear && c_is_linear {
            let (a_linear_var, a_coeff) = a.0[0];
            let (b_linear_var, b_coeff) = b.0[0];
            let (c_linear_var, c_coeff) = c.0[0];

            a_linear_var_coeff = a_coeff;
            b_linear_var_coeff = b_coeff;
            c_linear_var_coeff = c_coeff;

            is_quadratic = a_linear_var == b_linear_var && b_linear_var == c_linear_var;
        }
    }

    if is_quadratic {
        // something like (v - 1) * (v - 1) = (v - 1)
        // and we can make a quadratic gate

        let mut quadratic_term = a_linear_var_coeff;
        quadratic_term.mul_assign(&b_linear_var_coeff);

        let mut linear_term_0 = a_constant_term;
        linear_term_0.mul_assign(&b_linear_var_coeff);

        let mut linear_term_1 = b_constant_term;
        linear_term_1.mul_assign(&a_linear_var_coeff);

        let mut linear_term = linear_term_0;
        linear_term.add_assign(&linear_term_1);
        if c_is_linear {
            linear_term.sub_assign(&c_linear_var_coeff);
        }

        let mut constant_term = a_constant_term;
        constant_term.mul_assign(&b_constant_term);

        if c_constant_term != zero {
            constant_term.sub_assign(&c_constant_term);
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

fn get_first_variable_with_coeff<E: Engine, CS: ConstraintSystem<E>>(lc: &LinearCombination<E>) -> (bool, Variable, E::Fr) {
    let cs_one = CS::one();
    
    for (var, coeff) in lc.as_ref().iter() {
        if var != &cs_one {
            return (true, *var, *coeff);
        }
    }

    (false, cs_one, E::Fr::zero())
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

    // let _initial_len = deduped_vec.len();

    deduped_vec = deduped_vec.into_iter().filter(|(_var, coeff)| !coeff.is_zero()).collect();

    // let _final_len = deduped_vec.len();

    // if _initial_len != _final_len {
    //     println!("Encountered constraint with zero coeff for variable!");
    // }

    // assert!(deduped_vec.len() != 0);

    scratch.clear();

    LinearCombination(deduped_vec)
}

fn deduplicate_and_split_linear_term<E: Engine, CS: ConstraintSystem<E>>(
    lc: LinearCombination<E>,
    scratch: &mut HashMap<crate::cs::Variable, usize>
) -> (bool, E::Fr, bool, LinearCombination<E>) {
    assert!(scratch.is_empty());

    if lc.as_ref().len() == 0 {
        return (true, E::Fr::zero(), true, lc);
    }

    let cs_one = CS::one();
    let mut constant_term = E::Fr::zero();

    let mut deduped_vec: Vec<(crate::cs::Variable, E::Fr)> = Vec::with_capacity(lc.as_ref().len());

    for (var, coeff) in lc.0.into_iter() {
        if var != cs_one {
            if let Some(existing_index) = scratch.get(&var) {
                let (_, c) = &mut deduped_vec[*existing_index];
                c.add_assign(&coeff);
            } else {
                let new_idx = deduped_vec.len();
                deduped_vec.push((var, coeff));
                scratch.insert(var, new_idx);
            }
        } else {
            constant_term.add_assign(&coeff);
        }
    }

    // let _initial_len = deduped_vec.len();

    deduped_vec = deduped_vec.into_iter().filter(|(_var, coeff)| !coeff.is_zero()).collect();

    // let _final_len = deduped_vec.len();

    // if _initial_len != _final_len {
    //     println!("Encountered constraint with zero coeff for variable!");
    // }

    // assert!(deduped_vec.len() != 0);

    scratch.clear();

    let has_constant = !constant_term.is_zero();
    let lc_is_empty = deduped_vec.len() == 0;

    (has_constant, constant_term, lc_is_empty, LinearCombination(deduped_vec))
}

fn subtract_lcs_with_dedup_stable<E: Engine, CS: ConstraintSystem<E>>(
    lc_0: LinearCombination<E>,
    lc_1: LinearCombination<E>,
    scratch: &mut HashMap<crate::cs::Variable, usize>
) -> LinearCombination<E> {
    assert!(scratch.is_empty());

    if lc_0.as_ref().len() == 0 && lc_1.as_ref().len() == 0{
        return lc_0;
    }

    let mut deduped_vec: Vec<(crate::cs::Variable, E::Fr)> = Vec::with_capacity(lc_0.as_ref().len() + lc_1.as_ref().len());

    for (var, coeff) in lc_0.0.into_iter() {
        if let Some(existing_index) = scratch.get(&var) {
            let (_, c) = &mut deduped_vec[*existing_index];
            c.add_assign(&coeff);
        } else {
            let new_idx = deduped_vec.len();
            deduped_vec.push((var, coeff));
            scratch.insert(var, new_idx);
        }
    }

    for (var, coeff) in lc_1.0.into_iter() {
        if let Some(existing_index) = scratch.get(&var) {
            let (_, c) = &mut deduped_vec[*existing_index];
            c.sub_assign(&coeff);
        } else {
            let new_idx = deduped_vec.len();
            let mut coeff_negated = coeff;
            coeff_negated.negate();
            deduped_vec.push((var, coeff_negated));
            scratch.insert(var, new_idx);
        }
    }

    // let _initial_len = deduped_vec.len();

    deduped_vec = deduped_vec.into_iter().filter(|(_var, coeff)| !coeff.is_zero()).collect();

    // let _final_len = deduped_vec.len();

    // if _initial_len != _final_len {
    //     println!("Encountered constraint with zero coeff for variable!");
    // }

    // assert!(deduped_vec.len() != 0);

    scratch.clear();

    LinearCombination(deduped_vec)
}

fn subtract_variable_unchecked<E: Engine>(
    lc: &mut LinearCombination<E>,
    variable: Variable
) {
    let mut minus_one = E::Fr::one();
    minus_one.negate();

    lc.0.push((variable, minus_one));
}

fn split_constant_term<E: Engine, CS: ConstraintSystem<E>>(
    mut lc: LinearCombination<E>,
) -> (LinearCombination<E>, E::Fr) {
    if lc.as_ref().len() == 0 {
        return (lc, E::Fr::zero());
    }

    let mut idx = None;
    let cs_one = CS::one();
    let mut constant_coeff = E::Fr::zero();

    for (i, (var, coeff)) in lc.0.iter().enumerate() {
        if var == &cs_one {
            idx = Some(i);
            constant_coeff = *coeff;
            break;
        }
    }

    if let Some(idx) = idx {
        let _ = lc.0.swap_remove(idx);
        return (lc, constant_coeff);
    } else {
        return (lc, constant_coeff);
    }
}


pub struct Adaptor<'a, E: Engine, CS: PlonkConstraintSystem<E, GateCoefficients = [E::Fr; 6]> + 'a> {
    cs: &'a mut CS,
    hints: &'a Vec<(usize, TranspilationVariant)>,
    current_constraint_index: usize,
    current_hint_index: usize,
    scratch: HashSet<crate::cs::Variable>,
    // deduplication_scratch: HashMap<crate::cs::Variable, E::Fr>,
    deduplication_scratch: HashMap<crate::cs::Variable, usize>,
    _marker: std::marker::PhantomData<E>
}

impl<'a, E: Engine, CS: PlonkConstraintSystem<E, GateCoefficients = [E::Fr; 6]> + 'a> Adaptor<'a, E, CS> {
    // fn get_next_hint(&mut self) -> &(usize, TranspilationVariant<E>) {
    //     let current_hint_index = self.current_hint_index;
    //     let expected_constraint_index = self.current_constraint_index;

    //     let next_hint = &self.hints[current_hint_index];

    //     assert!(next_hint.0 == expected_constraint_index);

    //     self.current_hint_index += 1;
    //     self.current_constraint_index += 1;

    //     next_hint
    // }

    fn get_next_hint(&mut self) -> (usize, TranspilationVariant) {
        let current_hint_index = self.current_hint_index;
        let expected_constraint_index = self.current_constraint_index;

        let next_hint = self.hints[current_hint_index].clone();

        assert!(next_hint.0 == expected_constraint_index);

        self.current_hint_index += 1;
        self.current_constraint_index += 1;

        next_hint
    }
}

impl<'a, E: Engine, CS: PlonkConstraintSystem<E, GateCoefficients = [E::Fr; 6]> + 'a> crate::ConstraintSystem<E>
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
            _ => unreachable!("Map aux into aux"),
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
            _ => unreachable!("Map input into input"),
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
        let zero_fr = E::Fr::zero();
        let one_fr = E::Fr::one();
        let mut minus_one_fr = E::Fr::one();
        minus_one_fr.negate();

        let (_, hint) = { 
            self.get_next_hint() 
        };

        let _hint = hint.clone();

        // we need to determine the type of transformation constraint

        // let's handle trivial cases first

        // A or B or C are just constant terms

        let (a_has_constant, a_constant_term, a_lc_is_empty, a_lc) = deduplicate_and_split_linear_term::<E, Self>(a(crate::LinearCombination::zero()), &mut self.deduplication_scratch);
        let (b_has_constant, b_constant_term, b_lc_is_empty, b_lc) = deduplicate_and_split_linear_term::<E, Self>(b(crate::LinearCombination::zero()), &mut self.deduplication_scratch);
        let (c_has_constant, c_constant_term, c_lc_is_empty, c_lc) = deduplicate_and_split_linear_term::<E, Self>(c(crate::LinearCombination::zero()), &mut self.deduplication_scratch);

        let a_is_constant = a_has_constant & a_lc_is_empty;
        let b_is_constant = b_has_constant & b_lc_is_empty;
        let c_is_constant = c_has_constant & c_lc_is_empty;

        // debug_assert!(a_has_constant || !a_lc_is_empty);
        // debug_assert!(b_has_constant || !b_lc_is_empty);
        // debug_assert!(c_has_constant || !c_lc_is_empty);

        // let ann : String = _ann().into();
        // println!("Enforcing {}", ann);
        // println!("LC_A");
        // for (var, coeff) in a.as_ref().iter() {
        //     println!("{} * {:?}", coeff, var);
        // }
        // println!("LC_B");
        // for (var, coeff) in b.as_ref().iter() {
        //     println!("{} * {:?}", coeff, var);
        // }
        // println!("LC_C");
        // for (var, coeff) in c.as_ref().iter() {
        //     println!("{} * {:?}", coeff, var);
        // }

        let dummy_var = self.cs.get_dummy_variable();

        // variables are left, right, output
        // coefficients are left, right, output, multiplication, constant

        match hint {
            TranspilationVariant::IntoQuadraticGate => {
                let var = if !a_lc_is_empty {
                    convert_variable(a_lc.0[0].0)
                } else if !b_lc_is_empty {
                    convert_variable(b_lc.0[0].0)
                } else if !c_lc_is_empty {
                    convert_variable(c_lc.0[0].0)
                } else {
                    unreachable!();
                };

                let (is_quadratic, coeffs) = check_for_quadratic_gate(
                    &a_lc, 
                    &b_lc, 
                    &c_lc, 
                    a_constant_term, 
                    b_constant_term,
                    c_constant_term
                );

                debug_assert!(is_quadratic);

                let (c0, c1, c2) = coeffs;

                self.cs.new_gate(
                    (var, var, dummy_var),
                    [c1, zero_fr, zero_fr, c2, c0, zero_fr]
                ).expect("must make a quadratic gate");
            },
            TranspilationVariant::IntoMultiplicationGate(boxed_hints) => {
                // let ann: String = _ann().into();
                // if ann.contains("(a - b) * x == r - 1") {
                //     println!("{}", ann);
                // }

                let (t_a, t_b, t_c) = *boxed_hints;
                let mut q_m = one_fr;
                let mut q_c = one_fr;
                let a_var = match t_a {
                    hint @ TranspilationVariant::IntoSingleAdditionGate |
                    hint @ TranspilationVariant::IntoMultipleAdditionGates => {
                        let (new_a_var, a_coeff, _variant) = enforce_lc_as_gates(
                            self.cs,
                            a_lc,
                            one_fr,
                            a_constant_term,
                            true,
                        );

                        assert!(a_coeff == one_fr);

                        // q_m.mul_assign(&a_coeff);

                        assert!(_variant == hint);

                        new_a_var.expect("transpiler must create a new variable for LC A")
                    },
                    TranspilationVariant::LeaveAsSingleVariable => {
                        assert!(!a_lc_is_empty);
                        let (var, coeff) = a_lc.0[0];
                        q_m.mul_assign(&coeff); // collapse coeff before A*B

                        convert_variable(var)
                    },
                    _ => {unreachable!("{:?}", t_a)}
                };

                let b_var = match t_b {
                    hint @ TranspilationVariant::IntoSingleAdditionGate | 
                    hint @ TranspilationVariant::IntoMultipleAdditionGates => {
                        let (new_b_var, b_coeff, _variant) = enforce_lc_as_gates(
                            self.cs,
                            b_lc,
                            one_fr,
                            b_constant_term,
                            true,
                        );

                        assert!(b_coeff == one_fr);

                        // q_m.mul_assign(&b_coeff);

                        assert!(_variant == hint);

                        new_b_var.expect("transpiler must create a new variable for LC B")
                    },
                    TranspilationVariant::LeaveAsSingleVariable => {
                        assert!(!b_lc_is_empty);
                        let (var, coeff) = b_lc.0[0];
                        q_m.mul_assign(&coeff); // collapse coeffs before A*B

                        convert_variable(var)
                    },
                    _ => {unreachable!("{:?}", t_b)}
                };

                let (c_is_just_a_constant, c_var) = match t_c {
                    hint @ TranspilationVariant::IntoSingleAdditionGate | 
                    hint @ TranspilationVariant::IntoMultipleAdditionGates => {
                        let (new_c_var, c_coeff, _variant) = enforce_lc_as_gates(
                            self.cs,
                            c_lc,
                            one_fr,
                            c_constant_term,
                            true,
                        );

                        assert!(c_coeff == one_fr);

                        // q_c.mul_assign(&c_coeff);

                        assert!(_variant == hint);

                        (false, Some(new_c_var.expect("transpiler must create a new variable for LC C")))
                    },
                    TranspilationVariant::LeaveAsSingleVariable => {
                        assert!(!c_lc_is_empty);
                        let (var, coeff) = c_lc.0[0];
                        q_c = coeff;

                        (false, Some(convert_variable(var)))
                    },
                    TranspilationVariant::IsConstant => {
                        assert!(c_lc_is_empty);
                        assert!(c_has_constant);

                        (true, None)
                    },
                    _ => {unreachable!("{:?}", t_c)}
                };

                if c_is_just_a_constant {
                    let mut constant_term = c_constant_term;
                    constant_term.negate(); // - C

                    // A*B == constant
                    let t = self.cs.new_gate(
                        (a_var, b_var, dummy_var), 
                        [zero_fr, zero_fr, zero_fr, q_m, constant_term, zero_fr]
                    ); //.expect("must make a multiplication gate with C being constant");
                    if t.is_err() {
                        // let ann: String = _ann().into();
                        // println!("Enforcing {}", ann);
                        println!("Hint = {:?}", _hint);
                        panic!("Unsatisfied multiplication gate with C being constant");
                    }
                } else {
                    q_c.negate(); // - C

                    let c_var = c_var.expect("C must be a variable");
                    let t = self.cs.new_gate(
                        (a_var, b_var, c_var), 
                        [zero_fr, zero_fr, q_c, q_m, zero_fr, zero_fr]
                    ); //.expect("must make a multiplication gate");

                    if t.is_err() {
                        // let ann: String = _ann().into();
                        // println!("Enforcing {}", ann);
                        println!("A constant term = {}", a_constant_term);
                        println!("B constant term = {}", b_constant_term);
                        println!("C constant term = {}", c_constant_term);
                        println!("Hint = {:?}", _hint);
                        panic!("Unsatisfied multiplication gate");
                    }
                }
            },
            hint @ TranspilationVariant::IntoSingleAdditionGate |
            hint @ TranspilationVariant::IntoMultipleAdditionGates => {
                // let ann: String = _ann().into();
                // println!("Enforcing {}", ann);
                // println!("Hint is {:?}", hint);

                // these are simple enforcements that are not a part of multiplication gate
                // or merge of LCs

                if c_is_constant {
                    let lc = if !a_is_constant {
                        a_lc
                    } else if !b_is_constant {
                        b_lc
                    } else {
                        unreachable!("Either A or B LCs are constant");
                    };
    
                    let multiplier = if a_is_constant {
                        a_constant_term
                    } else if b_is_constant {
                        b_constant_term
                    } else {
                        unreachable!("Must take multiplier from A or B");
                    };
    
                    let mut free_constant_term = if a_is_constant {
                        b_constant_term
                    } else if b_is_constant {
                        a_constant_term
                    } else {
                        unreachable!("Either A or B LCs are constant");
                    };
    
                    free_constant_term.mul_assign(&multiplier);
                    free_constant_term.sub_assign(&c_constant_term);
    
                    let (_, _, _variant) = enforce_lc_as_gates(
                        self.cs,
                        lc,
                        multiplier,
                        free_constant_term,
                        false,
                    );

                    assert!(hint == _variant);
                } else {
                    // let ann: String = _ann().into();
                    // println!("Enforcing {}", ann);
                    // println!("Hint is {:?}", hint);

                    // c is not a constant and it's handled by MergeLCs
                    unreachable!();
                }
            },
            TranspilationVariant::IsConstant => {
                // let ann: String = _ann().into();
                // println!("Enforcing {}", ann);
                // println!("Hint is {:?}", hint);
                unreachable!()
            },
            TranspilationVariant::LeaveAsSingleVariable => {
                // let ann: String = _ann().into();
                // println!("Enforcing {}", ann);
                // println!("Hint is {:?}", hint);

                // we may have encounted this if something like variable == 0
                // but we use addition gate instead
                unreachable!()
            },
            TranspilationVariant::MergeLinearCombinations(merge_variant, merge_hint) => {
                let multiplier = if a_is_constant {
                    a_constant_term
                } else if b_is_constant {
                    b_constant_term
                } else {
                    unreachable!()
                };

                // assert!(coeff == one_fr);

                let mut free_constant_term;

                let lc_into_rewriting = match merge_variant {
                    MergeLcVariant::MergeACThroughConstantB => {
                        assert!(b_is_constant);
                        let mut final_lc = a_lc;
                        free_constant_term = a_constant_term;
                        if multiplier != one_fr {
                            for (_, c) in final_lc.0.iter_mut() {
                                c.mul_assign(&multiplier);
                            }
                            free_constant_term.mul_assign(&multiplier);
                        }

                        free_constant_term.sub_assign(&c_constant_term);

                        subtract_lcs_with_dedup_stable::<E, Self>(final_lc, c_lc, &mut self.deduplication_scratch)
                        // final_lc - &c
                    },
                    MergeLcVariant::MergeBCThroughConstantA => {
                        assert!(a_is_constant);
                        let mut final_lc = b_lc;
                        free_constant_term = b_constant_term;
                        if multiplier != one_fr {
                            for (_, c) in final_lc.0.iter_mut() {
                                c.mul_assign(&multiplier);
                            }
                            free_constant_term.mul_assign(&multiplier);
                        }

                        free_constant_term.sub_assign(&c_constant_term);

                        subtract_lcs_with_dedup_stable::<E, Self>(final_lc, c_lc, &mut self.deduplication_scratch)
                        // final_lc - &c
                    },  
                    MergeLcVariant::CIsTheOnlyMeaningful => {
                        free_constant_term = a_constant_term;
                        free_constant_term.mul_assign(&b_constant_term);
                        free_constant_term.negate();
                        free_constant_term.add_assign(&c_constant_term);

                        c_lc
                    },
                    _ => {
                        unreachable!()
                    }
                };

                let h = *merge_hint;

                match h {
                    hint @ TranspilationVariant::IntoSingleAdditionGate |
                    hint @ TranspilationVariant::IntoMultipleAdditionGates => {
                        let (new_c_var, _coeff, _variant) = enforce_lc_as_gates(
                            self.cs,
                            lc_into_rewriting,
                            one_fr,
                            free_constant_term,
                            false,
                        );

                        assert!(_coeff == one_fr);

                        assert!(new_c_var.is_none());
                        assert!(_variant == hint);
                    },
                    _ => {
                        unreachable!("{:?}", h);
                    }
                };
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

fn convert_variable(r1cs_variable: crate::Variable) -> PlonkVariable {
    let var = match r1cs_variable.get_unchecked() {
        crate::Index::Input(0) => {unreachable!("can not convert input variable number 0 (CS::one)")},
        crate::Index::Aux(0) => {unreachable!("can not convert aux variable labeled as 0 (taken by Plonk CS)")},
        crate::Index::Input(i) => PlonkVariable(PlonkIndex::Input(i)),
        crate::Index::Aux(i) => PlonkVariable(PlonkIndex::Aux(i)),
    };

    var
}

fn convert_variable_back(plonk_variable: PlonkVariable) -> crate::Variable {
    let var = match plonk_variable.get_unchecked() {
        crate::plonk::cs::variable::Index::Input(0) => {unreachable!("can not convert input variable number 0 (does not exist in plonk)")},
        crate::plonk::cs::variable::Index::Aux(0) => {unreachable!("can not convert aux variable labeled as 0 (does not exist in plonk, dummy gate)")},
        crate::plonk::cs::variable::Index::Input(i) => crate::Variable(crate::Index::Input(i)),
        crate::plonk::cs::variable::Index::Aux(i) => crate::Variable(crate::Index::Aux(i)),
    };

    var
}

use std::cell::Cell;

pub struct AdaptorCircuit<'a, E:Engine, C: crate::Circuit<E>>{
    circuit: Cell<Option<C>>,
    hints: &'a Vec<(usize, TranspilationVariant)>,
    _marker: std::marker::PhantomData<E>
}

impl<'a, E:Engine, C: crate::Circuit<E>> AdaptorCircuit<'a, E, C> {
    pub fn new<'b>(circuit: C, hints: &'b Vec<(usize, TranspilationVariant)>) -> Self 
        where 'b: 'a 
    {
        Self {
            circuit: Cell::new(Some(circuit)),
            hints: hints,
            _marker: std::marker::PhantomData
        }
    }
}

impl<'a, E: Engine, C: crate::Circuit<E>> PlonkCircuit<E, [E::Fr; 6]> for AdaptorCircuit<'a, E, C> {
    fn synthesize<CS: PlonkConstraintSystem<E, GateCoefficients = [E::Fr; 6]>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        let mut adaptor = Adaptor::<E, CS> {
            cs: cs,
            hints: self.hints,
            current_constraint_index: 0,
            current_hint_index: 0,
            scratch: HashSet::with_capacity((E::Fr::NUM_BITS * 2) as usize),
            deduplication_scratch: HashMap::with_capacity((E::Fr::NUM_BITS * 2) as usize),
            _marker: std::marker::PhantomData
        };

        let c = self.circuit.replace(None).expect("Must replace a circuit out from cell");

        match c.synthesize(&mut adaptor) {
            Err(_) => return Err(SynthesisError::AssignmentMissing),
            Ok(_) => {}
        };

        Ok(())
    }
}

#[test]
fn transpile_xor_using_new_adaptor() {
    use crate::tests::XORDemo;
    use crate::cs::Circuit;
    use crate::pairing::bn256::Bn256;
    use super::test_assembly::*;
    // use crate::plonk::plonk::generator::*;
    // use crate::plonk::plonk::prover::*;

    let c = XORDemo::<Bn256> {
        a: None,
        b: None,
        _marker: PhantomData
    };

    let mut transpiler = Transpiler::<Bn256>::new();

    c.synthesize(&mut transpiler).expect("sythesize into traspilation must succeed");

    let hints = transpiler.hints;

    for (constraint_id, hint) in hints.iter() {
        println!("Constraint {} into {:?}", constraint_id, hint);
    }

    // let c = XORDemo::<Bn256> {
    //     a: None,
    //     b: None,
    //     _marker: PhantomData
    // };

    let c = XORDemo::<Bn256> {
        a: Some(true),
        b: Some(true),
        _marker: PhantomData
    };

    let adapted_curcuit = AdaptorCircuit::new(c, &hints);

    let mut assembly = TestAssembly::<Bn256>::new();
    adapted_curcuit.synthesize(&mut assembly).expect("sythesize of transpiled into CS must succeed");
    assert!(assembly.is_satisfied());
    let num_gates = assembly.num_gates();
    println!("Transpiled into {} gates", num_gates);
    // assembly.finalize();

    // for (i, g) in assembly.aux_gates.iter().enumerate() {
    //     println!("Gate {} = {:?}", i, g);
    // }

    // let c = XORDemo::<Bn256> {
    //     a: Some(true),
    //     b: Some(true),
    //     _marker: PhantomData
    // };

    // println!("Trying to prove");

    // let adapted_curcuit = AdaptorCircuit::new(c, &hints);

    // let mut prover = ProvingAssembly::<Bn256>::new();
    // adapted_curcuit.synthesize(&mut prover).unwrap();
    // prover.finalize();

    // assert!(prover.is_satisfied());
}