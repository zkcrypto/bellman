use crate::pairing::{Engine};
use crate::sonic::cs::Backend;
use std::marker::PhantomData;
use std::iter::Peekable;

use crate::SynthesisError;
use crate::sonic::cs::SynthesisDriver;

use crate::sonic::cs::{Circuit, ConstraintSystem, Variable, LinearCombination, Coeff};

use crate::pairing::ff::Field;

use super::M;

pub struct NonassigningSynthesizer<E: Engine, B: Backend<E>> {
    backend: B,
    current_variable: Option<usize>,
    _marker: PhantomData<E>,
    q: usize,
    n: usize,
}

impl<E: Engine, B: Backend<E>>NonassigningSynthesizer<E, B> {
    pub fn new(backend: B) -> Self {
        Self {
            backend: backend,
            current_variable: None,
            _marker: PhantomData,
            q: 0,
            n: 0,
        }
    }
}

impl<E: Engine, B: Backend<E>> ConstraintSystem<E> for NonassigningSynthesizer<E, B> {
    const ONE: Variable = Variable::A(1);

    fn alloc<F>(&mut self, _value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>
    {
        match self.current_variable.take() {
            Some(index) => {
                let var_b = Variable::B(index);

                self.current_variable = None;

                Ok(var_b)
            },
            None => {
                self.n += 1;
                let index = self.n;
                self.backend.new_multiplication_gate();

                let var_a = Variable::A(index);

                self.current_variable = Some(index);

                Ok(var_a)
            }
        }
    }

    fn alloc_input<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>
    {
        let input_var = self.alloc(value)?;

        self.enforce_zero(LinearCombination::zero() + input_var);
        self.backend.new_k_power(self.q);

        Ok(input_var)
    }

    fn enforce_zero(&mut self, lc: LinearCombination<E>)
    {
        self.q += 1;
        let y = self.backend.new_linear_constraint();

        for (var, coeff) in lc.as_ref() {
            self.backend.insert_coefficient(*var, *coeff, &y);
        }
    }

    fn multiply<F>(&mut self, _values: F) -> Result<(Variable, Variable, Variable), SynthesisError>
    where
        F: FnOnce() -> Result<(E::Fr, E::Fr, E::Fr), SynthesisError>
    {
        self.n += 1;
        let index = self.n;
        self.backend.new_multiplication_gate();

        let a = Variable::A(index);
        let b = Variable::B(index);
        let c = Variable::C(index);

        Ok((a, b, c))
    }

    fn get_value(&self, var: Variable) -> Result<E::Fr, ()> {
        self.backend.get_var(var).ok_or(())
    }
}

pub struct Synthesizer<E: Engine, B: Backend<E>> {
    backend: B,
    current_variable: Option<usize>,
    _marker: PhantomData<E>,
    q: usize,
    n: usize,
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

    fn alloc_input<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>
    {
        let input_var = self.alloc(value)?;

        self.enforce_zero(LinearCombination::zero() + input_var);
        self.backend.new_k_power(self.q);

        Ok(input_var)
    }

    fn enforce_zero(&mut self, lc: LinearCombination<E>)
    {
        self.q += 1;
        let y = self.backend.new_linear_constraint();

        for (var, coeff) in lc.as_ref() {
            self.backend.insert_coefficient(*var, *coeff, &y);
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

impl<E: Engine, B: Backend<E>>Synthesizer<E, B> {
    pub fn new(backend: B) -> Self {
        Self {
            backend: backend,
            current_variable: None,
            _marker: PhantomData,
            q: 0,
            n: 0,
        }
    }
}

pub struct PermutationSynthesizer<E: Engine, B: Backend<E>> {
    backend: B,
    current_variable: Option<usize>,
    _marker: PhantomData<E>,
    q: usize,
    n: usize,

    // These vectors will hold, for all of the wires, the terms related to these
    // wires for each of the M permutation polynomials. The Coeff<E> is the
    // coefficient, and the usize is q, the index of the linear constraint and is
    // related to the power of Y in the s_1(X, Y) polynomial.
    pub a: Vec<[Option<(Coeff<E>, usize)>; M]>,
    pub b: Vec<[Option<(Coeff<E>, usize)>; M]>,
    pub c: Vec<[Option<(Coeff<E>, usize)>; M]>,
}

impl<E: Engine, B: Backend<E>> ConstraintSystem<E> for PermutationSynthesizer<E, B> {
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

                // Create slots for the new wires.
                self.a.push([None; M]);
                self.b.push([None; M]);
                self.c.push([None; M]);

                let var_a = Variable::A(index);

                self.backend.set_var(var_a, value)?;

                self.current_variable = Some(index);

                Ok(var_a)
            }
        }
    }

    fn alloc_input<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>
    {
        let input_var = self.alloc(value)?;

        self.enforce_zero(LinearCombination::zero() + input_var);
        // The new variable has all free slots, so this shouldn't create
        // more than one linear combination.
        self.backend.new_k_power(self.q);

        Ok(input_var)
    }

    fn enforce_zero(&mut self, lc: LinearCombination<E>)
    {
        // We just redirect things into the (recursing) enforce_equals method which
        // does the actual work. Annoyingly, we need to use dynamic dispatch on the
        // underlying iterator because once you've taken a Peekable<I> you can't get
        // the underlying iterator (since .next() may have been called on it) so
        // at each depth of recursion we'd end up with a new type, which is
        // impossible for the compiler to reason about.
        let lc = lc.as_ref();
        let lc: &mut Iterator<Item=&(Variable, Coeff<E>)> = &mut lc.into_iter();
        let lc = lc.peekable();

        self.enforce_equals(lc, None);
    }

    fn multiply<F>(&mut self, values: F) -> Result<(Variable, Variable, Variable), SynthesisError>
    where
        F: FnOnce() -> Result<(E::Fr, E::Fr, E::Fr), SynthesisError>
    {
        self.n += 1;
        let index = self.n;
        self.backend.new_multiplication_gate();

        // Create slots for the new wires.
        self.a.push([None; M]);
        self.b.push([None; M]);
        self.c.push([None; M]);

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

impl<E: Engine, B: Backend<E>> PermutationSynthesizer<E, B> {
    pub fn new(backend: B) -> Self {
        Self {
            backend: backend,
            current_variable: None,
            _marker: PhantomData,
            q: 0,
            n: 0,
            
            a: vec![],
            b: vec![],
            c: vec![],
        }
    }

    // Enforces that the value of `lhs` equals the value
    // of `rhs`, returning the value of the left hand side
    // as determined by the assignment. If rhs is none, it
    // is interpreted to be zero.
    fn enforce_equals<'a>(
        &mut self,
        mut lhs: Peekable<&mut Iterator<Item=&'a (Variable, Coeff<E>)>>,
        rhs: Option<Variable>
    ) -> Option<E::Fr>
    {
        // First, let's create a new linear constraint. We'll save its y value
        // for the backend and q as well.
        self.q += 1;
        let q = self.q;
        let y = self.backend.new_linear_constraint();
        let mut slots_available = [true; M];
        let mut num_slots_available = M;

        // If the caller is enforce_equals we need to return the value of the lhs
        // so that rhs can be assigned properly, so we keep track of it here.
        let mut current_value = if rhs.is_some() { Some(E::Fr::zero()) } else { None };

        // If rhs is Some, then we _need_ to involve it in this
        // linear constraint, so let's just handle it right away. (This also
        // helps avoid an infinite recursion issue described later.)
        if let Some(rhs) = rhs {
            self.emplace_variable(&mut slots_available, &y, rhs, Coeff::NegativeOne, q);
            num_slots_available -= 1;
        }

        // Iterate through the linear combination
        loop {
            if let Some(term) = lhs.next() {
                assert!(num_slots_available > 0);

                if num_slots_available == 1 && lhs.peek().is_some() {
                    // We'll be out of slots if we add this variable to the linear
                    // combination; instead, create an ephemeral variable to hold
                    // the value of the remaining terms and use that. Temporarily,
                    // give the variable "zero" value.
                    let ephemeral = self.alloc(|| Ok(E::Fr::zero())).expect("assignment is provided so this should not fail");

                    // One of the annoying "tricks" we have to embrace is that the ephemeral
                    // variable has all of its slots available, and so because it's the rhs
                    // when we recursively call `enforce_equals` we know that it will not trigger
                    // a condition in `emplace_variable` that results in the variable being
                    // duplicated; otherwise, the duplicate variable will have a value of zero
                    // and we'd have to somehow track all of the duplicates when we later assign.
                    let mut iter = Some(term).into_iter().chain(lhs);
                    let iter: &mut Iterator<Item=&(Variable, Coeff<E>)> = &mut iter;
                    let value = self.enforce_equals(iter.peekable(), Some(ephemeral));

                    // Set the correct ephemeral value right away
                    self.backend.set_var(ephemeral, || {
                        value.ok_or(SynthesisError::AssignmentMissing)
                    }).expect("assignment is provided so this should not fail");

                    // Fix the underlying assignment -- the c-wire value will change if the ephemeral
                    // value was a b-wire.
                    self.fix_variable_assignment(ephemeral);

                    // Now we emplace the variable into the linear combination.
                    self.emplace_variable(&mut slots_available, &y, ephemeral, Coeff::One, q);
                    num_slots_available -= 1;

                    match (&mut current_value, &value) {
                        (Some(ref mut current_value), Some(ref value)) => {
                            current_value.add_assign(&value);
                        },
                        _ => {
                            current_value = None;
                        }
                    }

                    assert!(num_slots_available == 0);

                    // We're done, so return.
                    return current_value;
                } else {
                    self.emplace_variable(&mut slots_available, &y, term.0, term.1, q);
                    num_slots_available -= 1;

                    match (&mut current_value, self.backend.get_var(term.0)) {
                        (Some(ref mut current_value), Some(mut value)) => {
                            term.1.multiply(&mut value);
                            current_value.add_assign(&value);
                        },
                        _ => {
                            current_value = None;
                        }
                    }
                }
            } else {
                // We're done, so return.
                return current_value;
            }
        }
    }

    // This takes a variable and coefficient and places it into a linear combination,
    // given a set of slots that are available, and updates the slot availability to
    // reflect which slot was chosen.
    fn emplace_variable(&mut self, slots_available: &mut [bool; M], y: &B::LinearConstraintIndex, var: Variable, coeff: Coeff<E>, q: usize)
    {
        // Get the slots for this wire.
        let wire_slots = self.get_wire_slots(var);

        // Let's handle the simple case where the linear combination and the
        // variable have a slot that coincides.
        let mut available_i = None;
        for i in 0..M {
            if slots_available[i] {
                available_i = Some(i);

                if wire_slots[i] {
                    self.emplace_slot(var, i, coeff, y, q);
                    slots_available[i] = false;
                    return;
                }
            }
        }

        let available_i = available_i.expect("there is always at least one slot open");

        // available_i corresponds to a slot that is available in the linear
        // combination; clearly, it is not available for the wire. In order
        // to rectify this, we will create a new wire with the same value.
        let ephemeral_value = self.backend.get_var(var);
        let ephemeral = self.alloc(|| {
            ephemeral_value.ok_or(SynthesisError::AssignmentMissing)
        }).expect("assignment is provided so this should not fail");

        // Now, we'll emplace the slot for _this_ variable.
        self.emplace_slot(ephemeral, available_i, coeff, y, q);
        slots_available[available_i] = false;

        // Next, we'll free up a slot in the original wire
        let free_i = (available_i + 1) % M;

        // by moving the term to the ephemeral wire.
        self.move_slot(free_i, var, ephemeral);

        // The original wire has slot free_i available now, and
        // the new wire has only available_i and (available_i + 1) % M
        // occupied. As long as M>=3, this means available_i + 2 % M
        // is a free wire for the ephemeral and it is distinct from
        // free_i! So, we can relate the ephemeral variable to the
        // original.
        let iter = [(var, Coeff::One), (ephemeral, Coeff::NegativeOne)];
        let mut iter = iter.into_iter();
        let iter: &mut Iterator<Item=&(Variable, Coeff<E>)> = &mut iter;
        self.enforce_equals(iter.peekable(), None);
    }

    // Move slot value from wire to another
    fn move_slot(&mut self, slot: usize, from: Variable, to: Variable) {
        let slot_val;
        {
            let from_vals = match from {
                Variable::A(index) => &mut self.a[index - 1],
                Variable::B(index) => &mut self.b[index - 1],
                Variable::C(index) => &mut self.c[index - 1],
            };

            if from_vals[slot].is_none() {
                // In this case, we do nothing.
                return;
            }

            slot_val = from_vals[slot].unwrap();
            from_vals[slot] = None;
        }

        // We need the backend to compute the cached y^q value for us,
        // if it needs it.
        let y = self.backend.get_for_q(slot_val.1);

        self.backend.insert_coefficient(from, -slot_val.0, &y); // Negate coefficient to undo
        
        {
            let to_vals = match to {
                Variable::A(index) => &mut self.a[index - 1],
                Variable::B(index) => &mut self.b[index - 1],
                Variable::C(index) => &mut self.c[index - 1],
            };

            to_vals[slot] = Some(slot_val);
            self.backend.insert_coefficient(to, slot_val.0, &y);
        }
    }

    // Place a coefficient in a slot
    fn emplace_slot(&mut self, var: Variable, slot_index: usize, coeff: Coeff<E>, y: &B::LinearConstraintIndex, q: usize)
    {
        let vals = match var {
            Variable::A(index) => &mut self.a[index - 1],
            Variable::B(index) => &mut self.b[index - 1],
            Variable::C(index) => &mut self.c[index - 1],
        };

        vals[slot_index] = Some((coeff, q));

        self.backend.insert_coefficient(var, coeff, &y);
    }

    // Get available slots for a wire
    fn get_wire_slots(&self, var: Variable) -> [bool; M] {
        let vals = match var {
            Variable::A(index) => &self.a[index - 1],
            Variable::B(index) => &self.b[index - 1],
            Variable::C(index) => &self.c[index - 1],
        };

        let mut slots = [true; M];
        for i in 0..M {
            if vals[i].is_some() {
                slots[i] = false;
            }
        }

        slots
    }

    // If a variable changes value, we probably need to adjust.
    fn fix_variable_assignment(&mut self, var: Variable) {
        let index = var.get_index();

        let a_value = self.backend.get_var(Variable::A(index));
        let b_value = self.backend.get_var(Variable::B(index));

        let c_value = match (a_value, b_value) {
            (Some(mut a), Some(b)) => {
                a.mul_assign(&b);
                Some(a)
            },
            _ => { None }
        };

        self.backend.set_var(Variable::C(index), || {
            c_value.ok_or(SynthesisError::AssignmentMissing)
        }).expect("assignment exists if the closure is called");
    }
}