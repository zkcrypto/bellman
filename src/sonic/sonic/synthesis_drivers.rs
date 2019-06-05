use std::marker::PhantomData;
use crate::sonic::cs::{Backend, SynthesisDriver};
use crate::pairing::{Engine};
use crate::sonic::cs::{Variable, Circuit, ConstraintSystem, LinearCombination};
use crate::SynthesisError;

use crate::pairing::ff::{Field};

use super::constraint_systems::{NonassigningSynthesizer, Synthesizer, PermutationSynthesizer};

pub struct Basic;

impl SynthesisDriver for Basic {
    fn synthesize<E: Engine, C: Circuit<E>, B: Backend<E>>(backend: B, circuit: &C) -> Result<(), SynthesisError> {
        let mut tmp: Synthesizer<E, B> = Synthesizer::new(backend);

        let one = tmp.alloc_input(|| Ok(E::Fr::one())).expect("should have no issues");

        match (one, <Synthesizer<E, B> as ConstraintSystem<E>>::ONE) {
            (Variable::A(1), Variable::A(1)) => {},
            _ => panic!("one variable is incorrect")
        }

        circuit.synthesize(&mut tmp)?;

        Ok(())
    }
}

pub struct Nonassigning;

impl SynthesisDriver for Nonassigning {
    fn synthesize<E: Engine, C: Circuit<E>, B: Backend<E>>(backend: B, circuit: &C) -> Result<(), SynthesisError> {
        let mut tmp: NonassigningSynthesizer<E, B> = NonassigningSynthesizer::new(backend);

        let one = tmp.alloc_input(|| Ok(E::Fr::one())).expect("should have no issues");

        match (one, <NonassigningSynthesizer<E, B> as ConstraintSystem<E>>::ONE) {
            (Variable::A(1), Variable::A(1)) => {},
            _ => panic!("one variable is incorrect")
        }

        circuit.synthesize(&mut tmp)?;

        Ok(())
    }
}

/*

In order to use the fully succinct version of Sonic, the resulting s(X, Y) polynomial
must be in a more "trivial" form

s(X, Y) = X^{-N - 1} Y^N s_1(X, Y) - X^N s_2(X, Y)

where

s_1(X, Y) = \sum\limits_{i=1}^N u'_i(Y) X^{-i + N + 1}
            + \sum\limits_{i=1}^N v'_i(Y) X^{i + N + 1}
            + \sum\limits_{i=1}^N w'_i(Y) X^{i + 2N + 1}
s_2(X, Y) = \sum\limits_{i=1}^N (Y^i + Y^{-i}) X^i

u'_i(Y) = \sum\limits_{q=1}^Q Y^q u_{q,i}
v'_i(Y) = \sum\limits_{q=1}^Q Y^q v_{q,i}
w'_i(Y) = \sum\limits_{q=1}^Q Y^q w_{q,i}

such that s_1(X, Y) can be expressed as the sum of M permutation polynomials.

It is trivial for the verifier to evaluate s_2(X, Y), since polynomials of the form
x + x^2 + x^3 + ... can be evaluated with a logarithmic number of field operations.

In order to get s_1(X, Y) into the form needed, each constituent permutation polynomial
is effectively of the form

s_j(X, Y) = \sum\limits_{i=1}^{3N+1} c_i X^i Y^\sigma_j(i)

where \sigma_j(i) defines the permutation. The X^i corresponds to the wire, and the
Y^\sigma_j(i) corresponds to the index of the linear constraint.

This effectively means that within each polynomial there can be only one particular
X^i term, and so wires can only appear in M different linear combinations. Further,
because there is only ever a particular Y^i term in each M permutation polynomial,
linear combinations can have only M wires.

In order to synthesize a constraint system into a form that supports this wonky
arrangement, we need M>=3. The general goal is to treat each permutation polynomial
as a "slot" and, when constructing linear constraints, keep track of which slots are
"occupied" by wires, either with respect to the wires themselves or with respect to
the linear combination as it is being assembled.

If the linear combination has more than M terms, then we need to recursively
construct ephemeral wires to hold the values of the remaining terms, and relate those
wires to those terms in new linear combinations.

Once our linear combinations are small enough to fit the terms into the M slots,
we eagerly shove the terms in. The easy case is when a slot is available for both
the wire and the linear combination. The remaining cases can be addressed generally
by imagining that the wire has no available slots. We will create a new ephemeral
wire that holds the same value as the original wire and use this wire to insert the
linear combination. Then, we'll swap one of the terms from another slot into the new
ephemeral wire, freeing a slot in the original wire. Then, we trivially have that the
new wire and old wire have distinct slots free (since M>=3) and so we can now force
that they become equal.

In terms of actually implementing this, things can get tricky. We don't want to end
up in a circumstance where we are infinitely recursing, which can happen depending on
the order we create linear combinations for the ephemeral variables.
*/
pub struct Permutation3;

impl SynthesisDriver for Permutation3 {
    fn synthesize<E: Engine, C: Circuit<E>, B: Backend<E>>(backend: B, circuit: &C) -> Result<(), SynthesisError> {
        let mut tmp: PermutationSynthesizer<E, B> = PermutationSynthesizer::new(backend);

        let one = tmp.alloc_input(|| Ok(E::Fr::one())).expect("should have no issues");

        match (one, <PermutationSynthesizer<E, B> as ConstraintSystem<E>>::ONE) {
            (Variable::A(1), Variable::A(1)) => {},
            _ => panic!("one variable is incorrect")
        }

        circuit.synthesize(&mut tmp)?;

        Ok(())
    }
}
