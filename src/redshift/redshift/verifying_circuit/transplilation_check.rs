#[cfg(test)]
mod test {
    use crate::redshift::redshift::adaptor::*;
    use crate::redshift::redshift::test_assembly::*;
    use crate::redshift::redshift::cs::Circuit as PlonkCircuit;
    use crate::cs::*;
    use crate::redshift::redshift::verifying_circuit::rescue_gadget::*;
    use crate::redshift::redshift::verifying_circuit::common::*;
    use crate::pairing::{Engine};
    use crate::pairing::ff::{Field};
    use crate::redshift::IOP::hashes::rescue::{RescueParams};


    struct RescueCircuit<E: Engine>{
        num_steps: usize,
        _marker: std::marker::PhantomData<E>
    }

    impl<E: Engine> Circuit<E> for RescueCircuit<E> {
        fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
            
            let mut rescue_gadget = RescueGadget::new(cs)?;

            let a_alloc : AllocatedNum<E> = AllocatedNum::alloc(cs, || Ok(E::Fr::zero()))?;
            let mut a: Num<E> = a_alloc.into();
            let b_alloc : AllocatedNum<E> = AllocatedNum::alloc(cs, || Ok(E::Fr::zero()))?;
            let mut b: Num<E> = b_alloc.into();

            for _ in 0..self.num_steps {
                rescue_gadget.absorb(cs, a)?;
                rescue_gadget.absorb(cs, b)?;
                a = rescue_gadget.squeeze(cs)?;

                let temp_alloc : AllocatedNum<E> = AllocatedNum::alloc(cs, || Ok(E::Fr::zero()))?;
                b = temp_alloc.into();
            }

            Ok(())
        }
    }

    #[test]
    fn test_rescue_hash() {
        println!("HERE!");

        use crate::pairing::bn256::Bn256;

        let c = RescueCircuit::<Bn256> {
            num_steps: 256,
            _marker: std::marker::PhantomData,
        };

       let mut transpiler = Transpiler::<Bn256>::new();
        println!("HERE!");
        c.synthesize(&mut transpiler).expect("sythesize into traspilation must succeed");
        println!("HERE!");
        let hints = transpiler.hints;

        for (constraint_id, hint) in hints.iter() {
            //println!("Constraint {} into {:?}", constraint_id, hint);
        }
        println!("HERE!");

        let c = RescueCircuit::<Bn256> {
            num_steps: 256,
            _marker: std::marker::PhantomData,
        };

        let adapted_curcuit = AdaptorCircuit::new(c, &hints);

        let mut assembly = TestAssembly::<Bn256>::new();
        adapted_curcuit.synthesize(&mut assembly).expect("sythesize of transpiled into CS must succeed");
        //assert!(assembly.is_satisfied(false));
        let num_gates = assembly.num_gates();
        println!("Transpiled into {} gates", num_gates);
    }
}