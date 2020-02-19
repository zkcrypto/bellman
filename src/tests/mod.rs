use crate::pairing::{
    Engine
};

use crate::pairing::ff:: {
    Field,
    PrimeField,
};

pub mod dummy_engine;
use self::dummy_engine::*;

use std::marker::PhantomData;

use crate::{
    Circuit,
    ConstraintSystem,
    SynthesisError
};

#[derive(Clone)]
pub(crate) struct XORDemo<E: Engine> {
    pub(crate) a: Option<bool>,
    pub(crate) b: Option<bool>,
    pub(crate) _marker: PhantomData<E>
}

impl<E: Engine> Circuit<E> for XORDemo<E> {
    fn synthesize<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<(), SynthesisError>
    {
        let a_var = cs.alloc(|| "a", || {
            if self.a.is_some() {
                if self.a.unwrap() {
                    Ok(E::Fr::one())
                } else {
                    Ok(E::Fr::zero())
                }
            } else {
                Err(SynthesisError::AssignmentMissing)
            }
        })?;

        cs.enforce(
            || "a_boolean_constraint",
            |lc| lc + CS::one() - a_var,
            |lc| lc + a_var,
            |lc| lc
        );

        let b_var = cs.alloc(|| "b", || {
            if self.b.is_some() {
                if self.b.unwrap() {
                    Ok(E::Fr::one())
                } else {
                    Ok(E::Fr::zero())
                }
            } else {
                Err(SynthesisError::AssignmentMissing)
            }
        })?;

        cs.enforce(
            || "b_boolean_constraint",
            |lc| lc + CS::one() - b_var,
            |lc| lc + b_var,
            |lc| lc
        );

        let c_var = cs.alloc_input(|| "c", || {
            if self.a.is_some() && self.b.is_some() {
                if self.a.unwrap() ^ self.b.unwrap() {
                    Ok(E::Fr::one())
                } else {
                    Ok(E::Fr::zero())
                }
            } else {
                Err(SynthesisError::AssignmentMissing)
            }
        })?;

        cs.enforce(
            || "c_xor_constraint",
            |lc| lc + a_var + a_var,
            |lc| lc + b_var,
            |lc| lc + a_var + b_var - c_var
        );

        Ok(())
    }
}

#[derive(Clone)]
pub(crate) struct TranspilationTester<E: Engine> {
    pub(crate) a: Option<E::Fr>,
    pub(crate) b: Option<E::Fr>,
}

impl<E: Engine> Circuit<E> for TranspilationTester<E> {
    fn synthesize<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<(), SynthesisError>
    {
        let a_var = cs.alloc(|| "a", || {
            if let Some(a_value) = self.a {
                Ok(a_value)
            } else {
                Err(SynthesisError::AssignmentMissing)
            }
        })?;

        cs.enforce(
            || "a is zero",
            |lc| lc + a_var,
            |lc| lc + CS::one(),
            |lc| lc
        );

        let b_var = cs.alloc(|| "b", || {
            if let Some(b_value) = self.b {
                Ok(b_value)
            } else {
                Err(SynthesisError::AssignmentMissing)
            }
        })?;

        cs.enforce(
            || "b is one",
            |lc| lc + b_var,
            |lc| lc + CS::one(),
            |lc| lc + CS::one()
        );

        let c_var = cs.alloc_input(|| "c", || {
            if let Some(a_value) = self.a {
                Ok(a_value)
            } else {
                Err(SynthesisError::AssignmentMissing)
            }
        })?;

        cs.enforce(
            || "a is equal to c",
            |lc| lc + a_var,
            |lc| lc + CS::one(),
            |lc| lc + c_var
        );

        Ok(())
    }
}

#[cfg(feature = "plonk")]
#[test]
fn transpile_xor() {
    use crate::pairing::bn256::Bn256;
    use crate::plonk::adaptor::alternative::Transpiler;

    let c = XORDemo::<Bn256> {
        a: None,
        b: None,
        _marker: PhantomData
    };

    let mut transpiler = Transpiler::new();

    c.synthesize(&mut transpiler).unwrap();
}

#[cfg(feature = "plonk")]
#[test]
fn transpile_test_circuit() {
    use crate::pairing::bn256::{Bn256, Fr};
    use crate::plonk::adaptor::alternative::*;
    use crate::plonk::plonk::prover::*;

    let c = TranspilationTester::<Bn256> {
        a: Some(Fr::zero()),
        b: Some(Fr::one()),
    };

    let mut transpiler = Transpiler::new();

    c.clone().synthesize(&mut transpiler).unwrap();

    let hints = transpiler.into_hints();

    let adapted_curcuit = AdaptorCircuit::new(c.clone(), &hints);

    use crate::plonk::cs::Circuit as PlonkCircuit;

    let mut prover = ProvingAssembly::<Bn256>::new();
    adapted_curcuit.synthesize(&mut prover).unwrap();
    prover.finalize();

    println!("Checking if is satisfied");
    assert!(prover.is_satisfied());
}

