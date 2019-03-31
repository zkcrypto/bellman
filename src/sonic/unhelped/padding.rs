use crate::pairing::ff::{Field};
use crate::pairing::{Engine, CurveProjective};
use std::marker::PhantomData;

use crate::sonic::cs::{Backend};
use crate::sonic::cs::{Coeff, Variable, LinearCombination};
use crate::sonic::util::*;
use crate::sonic::util::*;
use crate::sonic::cs::{SynthesisDriver};
use crate::Circuit as BellmanCircuit;
use crate::sonic::sonic::AdaptorCircuit;
use crate::sonic::cs::Circuit;
use crate::sonic::cs::ConstraintSystem;
use crate::sonic::cs::Nonassigning;
use crate::SynthesisError;

/*
s_1(X, Y) =   \sum\limits_{i=1}^N u_i(Y) X^{N + 1 - i}
          + \sum\limits_{i=1}^N v_i(Y) X^{N + 1 + i}
          + \sum\limits_{i=1}^N w_i(Y) X^{2N + 1 + i}

where

    u_i(Y) =        \sum\limits_{q=1}^Q Y^{q} u_{i,q}
    v_i(Y) =        \sum\limits_{q=1}^Q Y^{q} v_{i,q}
    w_i(Y) =        \sum\limits_{q=1}^Q Y^{q} w_{i,q}

s_1(X, Y) = \sum\limits_{i=1}^(3N + 1) [u_{N + 1 - i}(Y), v_{i - N - 1}(Y), w_{i - 2N - 1}(Y)] X^{i}

where [] means concatenation

if we open up both sums a little it would look like

// q = 1,
Y * ( X * u_{N, 1} + X^{N + 1} * v_{1, 1} + X^{2N + 1} * w{1, 1}) = Y * (k_0 * X + k_1 * X^{N + 1} + k_2 * X^{2N + 1})
and for permutation where should exist another term over Y that would have the same structure, but with coefficients permuted, e.g.
Y^{p_1} * (k_1 * X + k_2 * X^{N + 1} + k_0 * X^{2N + 1}) and Y^{p_2} * (k_2 * X + k_0 * X^{N + 1} + k_1 * X^{2N + 1})
that would result in a sum 

  X * (k_0 * Y + k_1 * Y^{p_1} + k_2 * Y^{p_2}) 
+ X^{N + 1} * (k_1 * Y + k_2 * Y^{p_1} + k_0 * Y^{p_2})
+ X^{2N + 1} * (k_2 * Y + k_0 * Y^{p_1} + k_1 * Y^{p_2})

and permutations would look like 
                                [k_0, k_1, k_2]
                                [1  , p_1, p_2]

                                [k_0, k_1, k_2]
                                [p_2, 1  , p_1]

                                [k_0, k_1, k_2]
                                [p_1, p_2, 1  ]

that would naively mean that k_0 should appear in constraint number 1   for variable number 1
                                                  constraint number p_1 for variable number N + 1
                                                  constraint number p_2 for variable number 2N + 1

restructuring strategy:

where u_{i, q} is a coefficient in a linear constraint for an A type variable number i
that corresponds to the qth multiplication gate

to make s_1 representable as a permutation we first must synthesize all the normal constraints,
then make what would look like a cyclic shift + expansion

- imagine that there were originally N variables
- variable A(i) in linear constraint number q had a coefficient of u{i, q}
- add a variable B(i+n) that would have a number 

*/

pub struct Debugging<E> {
    constraint_num: usize,
    u: Vec<String>,
    v: Vec<String>,
    w: Vec<String>,
    _marker: std::marker::PhantomData<E>
}

impl<'a, E: Engine> Backend<E> for &'a mut Debugging<E> {
    fn new_linear_constraint(&mut self) {
        self.constraint_num += 1;
        self.u.push("".to_string());
        self.v.push("".to_string());
        self.w.push("".to_string());
    }

    fn insert_coefficient(&mut self, var: Variable, coeff: Coeff<E>) {
        let one = E::Fr::one();
        let mut minus_one = one;
        minus_one.negate();
        match var {
            Variable::A(index) => {
                let acc = &mut self.u[self.constraint_num - 1];
                match coeff {
                    Coeff::Zero => { },
                    Coeff::One => {
                        acc.push_str(&format!(" + A{}", index));
                    },
                    Coeff::NegativeOne => {
                        acc.push_str(&format!(" - A{}", index));
                    },
                    Coeff::Full(val) => {
                        if val == one {
                            acc.push_str(&format!(" + A{}", index));
                        } else if val == minus_one {
                            acc.push_str(&format!(" - A{}", index));
                        } else {
                            acc.push_str(&format!(" + {}*A{}", val, index));
                        }
                    }
                }
            }
            Variable::B(index) => {
                let acc = &mut self.v[self.constraint_num - 1];
                match coeff {
                    Coeff::Zero => { },
                    Coeff::One => {
                        acc.push_str(&format!(" + B{}", index));
                    },
                    Coeff::NegativeOne => {
                        acc.push_str(&format!(" - B{}", index));
                    },
                    Coeff::Full(val) => {
                        if val == one {
                            acc.push_str(&format!(" + B{}", index));
                        } else if val == minus_one {
                            acc.push_str(&format!(" - B{}", index));
                        } else {
                            acc.push_str(&format!(" + {}*B{}", val, index));
                        }
                    }
                }
            }
            Variable::C(index) => {
                let acc = &mut self.w[self.constraint_num - 1];
                match coeff {
                    Coeff::Zero => { },
                    Coeff::One => {
                        acc.push_str(&format!(" + C{}", index));
                    },
                    Coeff::NegativeOne => {
                        acc.push_str(&format!(" - C{}", index));
                    },
                    Coeff::Full(val) => {
                        if val == one {
                            acc.push_str(&format!(" + C{}", index));
                        } else if val == minus_one {
                            acc.push_str(&format!(" - C{}", index));
                        } else {
                            acc.push_str(&format!(" + {}*C{}", val, index));
                        }
                    }
                }
            }
        };
    }
}

pub struct Padding;

impl SynthesisDriver for Padding {
    fn synthesize<E: Engine, C: Circuit<E>, B: Backend<E>>(backend: B, circuit: &C) -> Result<(), SynthesisError> {
        struct Synthesizer<E: Engine, B: Backend<E>> {
            backend: B,
            current_variable: Option<usize>,
            _marker: PhantomData<E>,
            q: usize,
            n: usize,
        }

        impl<E: Engine, B: Backend<E>>Synthesizer<E, B> {
            fn purge_current_var(&mut self) {
                match self.current_variable.take() {
                    Some(index) => {
                        let var_a = Variable::A(index);
                        let var_b = Variable::B(index);
                        let var_c = Variable::C(index);

                        let mut product = None;

                        let value_a = self.backend.get_var(var_a);

                        self.backend.set_var(var_b, || {
                            let value_b = E::Fr::one();
                            product = Some(value_a.ok_or(SynthesisError::AssignmentMissing)?);
                            product.as_mut().map(|product| product.mul_assign(&value_b));

                            Ok(value_b)
                        }).expect("should exist by now");

                        self.backend.set_var(var_c, || {
                            product.ok_or(SynthesisError::AssignmentMissing)
                        }).expect("should exist by now");

                        self.current_variable = None;
                    },
                    _ => {}
                }
            }

            fn alloc_one(&mut self) -> Variable {
                self.n += 1;
                let index = self.n;
                assert_eq!(index, 1);
                self.backend.new_multiplication_gate();

                let var_a = Variable::A(1);
                let var_b = Variable::B(1);
                let var_c = Variable::C(1);

                self.backend.set_var(var_a, || {
                    Ok(E::Fr::one())
                }).expect("should exist by now");

                self.backend.set_var(var_b, || {
                    Ok(E::Fr::one())
                }).expect("should exist by now");

                self.backend.set_var(var_c, || {
                    Ok(E::Fr::one())
                }).expect("should exist by now");

                self.q += 1;
                self.backend.new_linear_constraint();
                self.backend.insert_coefficient(var_a, Coeff::One);
                self.backend.insert_coefficient(var_b, Coeff::One);
                self.backend.insert_coefficient(var_c, Coeff::NegativeOne);
                self.backend.new_k_power(self.q);

                var_a
            }
        }

        impl<E: Engine, B: Backend<E>> ConstraintSystem<E> for Synthesizer<E, B> {
            const ONE: Variable = Variable::A(1);

            fn alloc<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
            where
                F: FnOnce() -> Result<E::Fr, SynthesisError>
            {
                match self.current_variable.take() {
                    Some(index) => {
                        let var_a = Variable::A(index);
                        let var_b = Variable::B(index);
                        let var_c = Variable::C(index);

                        let mut product = None;

                        let value_a = self.backend.get_var(var_a);

                        self.backend.set_var(var_b, || {
                            let value_b = value()?;
                            product = Some(value_a.ok_or(SynthesisError::AssignmentMissing)?);
                            product.as_mut().map(|product| product.mul_assign(&value_b));

                            Ok(value_b)
                        })?;

                        self.backend.set_var(var_c, || {
                            product.ok_or(SynthesisError::AssignmentMissing)
                        })?;

                        self.current_variable = None;

                        Ok(var_b)
                    },
                    None => {
                        self.n += 1;
                        let index = self.n;
                        self.backend.new_multiplication_gate();

                        let var_a = Variable::A(index);

                        self.backend.set_var(var_a, value)?;

                        self.current_variable = Some(index);

                        Ok(var_a)
                    }
                }
            }

            // TODO: allocate input without spawning extra constraints
            fn alloc_input<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
            where
                F: FnOnce() -> Result<E::Fr, SynthesisError>
            {
                // self.purge_current_var();
                // self.n += 1;
                // self.backend.new_multiplication_gate();

                // let index = self.n;

                // let var = Variable::A::(index);

                // self.q += 1;
                // self.backend.new_k_power(self.q);
                // self.backend.self.backend.insert_coefficient(new_var, Coeff::One);

                // it's always going to be 
                let input_var = self.alloc(value)?;

                self.enforce_zero(LinearCombination::zero() + input_var);
                self.backend.new_k_power(self.q-2);
                self.backend.new_k_power(self.q-1);
                self.backend.new_k_power(self.q);

                Ok(input_var)
            }

            fn enforce_zero(&mut self, lc: LinearCombination<E>)
            {
                self.q += 1;
                self.backend.new_linear_constraint();

                for (var, coeff) in lc.as_ref() {
                    self.backend.insert_coefficient(*var, *coeff);
                }

                // now we need to "rotate" a linear constraint by allocating more dummy variables, so ensuring
                // that if for some q (index of LC) there is a coefficient C in front of a variable A(i) (that will result in a term ~ C*Y^{q}*X^{i})
                // then there will be some other q' where there is a coefficient C in front of the variable B(i)
                // (that will result in a term ~ C*Y^{q'}*X^{i+N}) and another q'' with C in front of C(i)
                // (that will result in a term ~ C*Y^{q''}*X^{i+2N}), so S polynomial is indeed a permutation

                // allocate at max 1 variable to later work with whole gates directly

                self.purge_current_var();

                use std::collections::HashMap;

                // A -> B, B -> C, C -> A
                {
                    self.q += 1;
                    self.backend.new_linear_constraint();

                    let mut allocation_map = HashMap::with_capacity(lc.as_ref().len());
                    let mut expected_new_index = self.n + 1;

                    // determine size of the map
                    for (var, _) in lc.as_ref() {
                        match var {
                            Variable::A(index) => {
                                if allocation_map.get(index).is_none() && *index != 1 {
                                    allocation_map.insert(*index, expected_new_index);
                                    expected_new_index += 1;
                                    println!("A{} -> B{}", index, expected_new_index);
                                }
                            },
                            Variable::B(index) => {
                                if allocation_map.get(index).is_none() && *index != 2 {
                                    allocation_map.insert(*index, expected_new_index);
                                    expected_new_index += 1;
                                    println!("B{} -> C{}", index, expected_new_index);
                                }
                            },
                            Variable::C(index) => {
                                if allocation_map.get(index).is_none() && *index != 3 {
                                    allocation_map.insert(*index, expected_new_index);
                                    expected_new_index += 1;
                                    println!("C{} -> A{}", index, expected_new_index);
                                }
                            }
                        }
                    }

                    for _ in 0..allocation_map.len() {
                        self.backend.new_multiplication_gate();
                        self.n += 1;
                    }

                    for (index, new_index) in allocation_map.iter() {
                        let var_a = Variable::A(*new_index);
                        let var_b = Variable::B(*new_index);
                        let var_c = Variable::C(*new_index);

                        // A -> B, B -> C, C -> A
                        let b_val = self.backend.get_var(Variable::A(*index));
                        let c_val = self.backend.get_var(Variable::B(*index));
                        let a_val = self.backend.get_var(Variable::C(*index));

                        self.backend.set_var(var_a, || {
                            let value = a_val.ok_or(SynthesisError::AssignmentMissing)?;

                            Ok(value)
                        }).expect("should exist by now");

                        self.backend.set_var(var_b, || {
                            let value = b_val.ok_or(SynthesisError::AssignmentMissing)?;

                            Ok(value)
                        }).expect("should exist by now");

                        self.backend.set_var(var_c, || {
                            let value = c_val.ok_or(SynthesisError::AssignmentMissing)?;

                            Ok(value)
                        }).expect("should exist by now");

                    }

                    // A -> B, B -> C, C -> A
                    for (var, coeff) in lc.as_ref() {
                        let new_var = match var {
                            Variable::A(index) => {
                                let var = if *index == 1 {
                                    Variable::B(2)
                                } else {
                                    let new_index = allocation_map.get(index).unwrap();
                                    Variable::B(*new_index)
                                };

                                var
                            },
                            Variable::B(index) => {
                                let var = if *index == 2 {
                                    Variable::C(3)
                                } else {
                                    let new_index = allocation_map.get(index).unwrap();
                                    Variable::C(*new_index)
                                };

                                var
                            },
                            Variable::C(index) => {
                                let var = if *index == 3 {
                                    Variable::A(1)
                                } else {
                                    let new_index = allocation_map.get(index).unwrap();
                                    Variable::A(*new_index)
                                };

                                var
                            }
                        };

                        self.backend.insert_coefficient(new_var, *coeff);
                    }
                }

                // A -> C, B -> A, C -> B
                {
                    self.q += 1;
                    self.backend.new_linear_constraint();

                    let mut allocation_map = HashMap::with_capacity(lc.as_ref().len());
                    let mut expected_new_index = self.n + 1;

                    // determine size of the map
                    for (var, _) in lc.as_ref() {
                        match var {
                            Variable::A(index) => {
                                if allocation_map.get(index).is_none() && *index != 1 {
                                    allocation_map.insert(*index, expected_new_index);
                                    expected_new_index += 1;
                                    println!("A{} -> C{}", index, expected_new_index);
                                }
                            },
                            Variable::B(index) => {
                                if allocation_map.get(index).is_none() && *index != 2 {
                                    allocation_map.insert(*index, expected_new_index);
                                    expected_new_index += 1;
                                    println!("B{} -> A{}", index, expected_new_index);
                                }
                            },
                            Variable::C(index) => {
                                if allocation_map.get(index).is_none() && *index != 3 {
                                    allocation_map.insert(*index, expected_new_index);
                                    expected_new_index += 1;
                                    println!("C{} -> B{}", index, expected_new_index);
                                }
                            }
                        }
                    }
                    
                    for _ in 0..allocation_map.len() {
                        self.backend.new_multiplication_gate();
                        self.n += 1;
                    }

                    // A -> C, B -> A, C -> B
                    for (index, new_index) in allocation_map.iter() {
                        let var_a = Variable::A(*new_index);
                        let var_b = Variable::B(*new_index);
                        let var_c = Variable::C(*new_index);

                        let b_val = self.backend.get_var(Variable::C(*index));
                        let c_val = self.backend.get_var(Variable::A(*index));
                        let a_val = self.backend.get_var(Variable::B(*index));

                        self.backend.set_var(var_a, || {
                            let value = a_val.ok_or(SynthesisError::AssignmentMissing)?;

                            Ok(value)
                        }).expect("should exist by now");

                        self.backend.set_var(var_b, || {
                            let value = b_val.ok_or(SynthesisError::AssignmentMissing)?;

                            Ok(value)
                        }).expect("should exist by now");

                        self.backend.set_var(var_c, || {
                            let value = c_val.ok_or(SynthesisError::AssignmentMissing)?;

                            Ok(value)
                        }).expect("should exist by now");
                    }

                    // A -> C, B -> A, C -> B
                    for (var, coeff) in lc.as_ref() {
                        let new_var = match var {
                            Variable::A(index) => {
                                let var = if *index == 1 {
                                    Variable::C(3)
                                } else {
                                    let new_index = allocation_map.get(index).unwrap();
                                    Variable::C(*new_index)
                                };

                                var
                            },
                            Variable::B(index) => {
                                let var = if *index == 2 {
                                    Variable::A(1)
                                } else {
                                    let new_index = allocation_map.get(index).unwrap();
                                    Variable::A(*new_index)
                                };

                                var
                            },
                            Variable::C(index) => {
                                let var = if *index == 3 {
                                    Variable::B(2)
                                } else {
                                    let new_index = allocation_map.get(index).unwrap();
                                    Variable::B(*new_index)
                                };

                                var
                            }
                        };

                        self.backend.insert_coefficient(new_var, *coeff);
                    }
                }
            }

            fn multiply<F>(&mut self, values: F) -> Result<(Variable, Variable, Variable), SynthesisError>
            where
                F: FnOnce() -> Result<(E::Fr, E::Fr, E::Fr), SynthesisError>
            {
                self.n += 1;
                let index = self.n;
                self.backend.new_multiplication_gate();

                let a = Variable::A(index);
                let b = Variable::B(index);
                let c = Variable::C(index);

                let mut b_val = None;
                let mut c_val = None;

                self.backend.set_var(a, || {
                    let (a, b, c) = values()?;

                    b_val = Some(b);
                    c_val = Some(c);

                    Ok(a)
                })?;

                self.backend.set_var(b, || {
                    b_val.ok_or(SynthesisError::AssignmentMissing)
                })?;

                self.backend.set_var(c, || {
                    c_val.ok_or(SynthesisError::AssignmentMissing)
                })?;

                Ok((a, b, c))
            }

            fn get_value(&self, var: Variable) -> Result<E::Fr, ()> {
                self.backend.get_var(var).ok_or(())
            }
        }

        let mut tmp: Synthesizer<E, B> = Synthesizer {
            backend: backend,
            current_variable: None,
            _marker: PhantomData,
            q: 0,
            n: 0,
        };

        let one = tmp.alloc_input(|| Ok(E::Fr::one())).expect("should have no issues");

        match (one, <Synthesizer<E, B> as ConstraintSystem<E>>::ONE) {
            (Variable::A(1), Variable::A(1)) => {},
            _ => panic!("one variable is incorrect")
        }

        circuit.synthesize(&mut tmp)?;

        println!("Done synthesizing, N = {}, Q = {}", tmp.n, tmp.q);

        Ok(())
    }
}

pub fn constraints_info<E: Engine, C: BellmanCircuit<E> + Clone>(
    circuit: C,
)
{
    let adapted_circuit = AdaptorCircuit(circuit);

    create_constraints_info::<_, _, Nonassigning>(&adapted_circuit)
}

pub fn constraints_padding_info<E: Engine, C: BellmanCircuit<E> + Clone>(
    circuit: C,
)
{
    let adapted_circuit = AdaptorCircuit(circuit);

    create_constraints_info::<_, _, Padding>(&adapted_circuit)
}

pub fn create_constraints_info<E: Engine, C: Circuit<E>, S: SynthesisDriver>(
    circuit: &C,
)
{
    let mut backend = Debugging::<E> {
        constraint_num: 0,
        u: vec![],
        v: vec![],
        w: vec![],
        _marker: std::marker::PhantomData
    };

    S::synthesize(&mut backend, circuit).unwrap();

    
    for (i, ((u, v), w)) in backend.u.iter()
                            .zip(backend.v.iter())
                            .zip(backend.w.iter())
                            .enumerate()
    {
        println!("Constraint {}: 0 = {}{}{}", i, u, v, w);
    }
}

#[test]
fn my_fun_circuit_test() {
    use crate::pairing::ff::PrimeField;
    use crate::pairing::bls12_381::{Bls12, Fr};

    struct MyCircuit;

    impl<E: Engine> Circuit<E> for MyCircuit {
        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            let (a, b, _) = cs.multiply(|| {
                Ok((
                    E::Fr::from_str("10").unwrap(),
                    E::Fr::from_str("20").unwrap(),
                    E::Fr::from_str("200").unwrap(),
                ))
            })?;

            cs.enforce_zero(LinearCombination::from(a) + a - b);

            let multiplier = cs.alloc_input(|| Ok(E::Fr::from_str("20").unwrap()))?;

            cs.enforce_zero(LinearCombination::from(b) - multiplier);

            Ok(())
        }
    }

    create_constraints_info::<Bls12, _, Nonassigning>(&MyCircuit);
    println!("---------------");
    create_constraints_info::<Bls12, _, Padding>(&MyCircuit);
}