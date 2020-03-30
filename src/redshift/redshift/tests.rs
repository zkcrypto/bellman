#[cfg(test)]
mod test {
    use crate::redshift::redshift::cs::*;
    use crate::redshift::redshift::generators::*;
    use crate::redshift::redshift::prover::*;
    use crate::redshift::redshift::verifier::*;
    use crate::redshift::redshift::data_structures::*;
    use crate::redshift::redshift::utils::*;

    use crate::redshift::IOP::FRI::coset_combining_fri::*;
    use crate::redshift::IOP::FRI::coset_combining_fri::precomputation::*;
    use crate::redshift::partial_reduction_field::*;
    use crate::redshift::partial_reduction_field::proth_engine::Transparent252;
    use crate::redshift::partial_reduction_field::proth::Fr;
    use crate::redshift::IOP::oracle::*;
    use crate::redshift::IOP::channel::*;
    use crate::redshift::fft::cooley_tukey_ntt::*;

    use crate::pairing::ff::{Field, PrimeField};
    use crate::pairing::{Engine};

    use crate::{SynthesisError};
    use std::marker::PhantomData;
    use crate::multicore::*;

    #[derive(Clone)]
    struct BenchmarkCircuit<E: Engine>{
        num_steps: usize,
        a: E::Fr,
        b: E::Fr,
        _marker: std::marker::PhantomData<E>
    }

    impl<E: Engine> Circuit<E> for BenchmarkCircuit<E> {
        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            // yeah, fibonacci...
            
            let mut a = cs.alloc_input(|| {
                Ok(self.a)
            })?;

            let mut b = cs.alloc_input(|| {
                Ok(self.b)
            })?;

            let mut a_value;
            let mut b_value = self.b.clone();
            let mut c_value = self.a.clone();
            c_value.add_assign(&b_value);
            let mut c;

            let one = E::Fr::one();
            let mut negative_one = one;
            negative_one.negate();

            for _ in 0..self.num_steps {
               
                c = cs.alloc(|| {
                    Ok(c_value)
                })?;

                cs.enforce_zero_3((a, b, c), (one, one, negative_one))?;

                a = b;
                b = c;

                a_value = b_value;
                b_value = c_value;
                c_value.add_assign(&a_value);
            }

            Ok(())
        }
    }

    fn test_redshift_template<E: Engine, I: Oracle<E::Fr>, T: Channel<E::Fr, Input = I::Commitment>>(
        a: E::Fr,
        b: E::Fr,
        num_steps: usize,
        lde_factor: usize,
        r: usize,
        collapsing_factor : usize,
        output_coeffs_at_degree_plus_one: usize,
    ) -> Result<bool, SynthesisError>
    where E::Fr : PartialTwoBitReductionField 
    {
        let mut params = FriParams {
            lde_factor,
            R: r,
            collapsing_factor,
            final_degree_plus_one: output_coeffs_at_degree_plus_one,
            // initial degree os set by generator
            initial_degree_plus_one : 0,
        };

        let circuit = BenchmarkCircuit::<E> {
            num_steps,
            a,
            b,
            _marker: std::marker::PhantomData::<E>
        };

        let omegas_bitreversed = BitReversedOmegas::<E::Fr>::new_for_domain_size(num_steps.next_power_of_two());
        let mut channel = T::new();

        let (_setup, setup_precomp) = setup_with_precomputations::<E, BenchmarkCircuit<E>,  BitReversedOmegas<E::Fr>, I, T>(
            &circuit,
            &mut params,
            &omegas_bitreversed,
            &mut channel,
        )?;

        let omegas_inv_bitreversed = <OmegasInvBitreversed::<E::Fr> as CTPrecomputations::<E::Fr>>::new_for_domain_size(num_steps.next_power_of_two());
        let omegas_inv_bitreversed_for_fri = <CosetOmegasInvBitreversed::<E::Fr> as FriPrecomputations::<E::Fr>>::new_for_domain_size(num_steps.next_power_of_two() * lde_factor);

        let proof = prove_with_setup_precomputed::<E, BenchmarkCircuit<E>, BitReversedOmegas<E::Fr>, 
            OmegasInvBitreversed::<E::Fr>, CosetOmegasInvBitreversed::<E::Fr>, I, T> (
            &circuit,
            &setup_precomp, 
            &params, 
            &omegas_bitreversed, 
            &omegas_inv_bitreversed,
            &omegas_inv_bitreversed_for_fri
        )?;

        let is_valid = verify_proof::<E, I, T>(
            proof,
            &[a, b],
            &setup_precomp,
            &params,
        );

        is_valid
    }

    #[test]
    fn test_redshift_with_blake() {

        use crate::redshift::IOP::oracle::coset_combining_blake2s_tree::*;
        use crate::redshift::IOP::channel::blake_channel::*;

        type E = Transparent252;
        type O = FriSpecificBlake2sTree<Fr>;
        type T = StatelessBlake2sChannel<Fr>;

        let res = test_redshift_template::<E, O, T>(
            Fr::one(),
            Fr::one(),
            1000,
            16,
            4,
            1,
            1);

        match res {
            Ok(valid) => assert_eq!(valid, true),
            Err(_) => println!("Some erro has been occured!"),
        };       
    }

    #[test]
    fn test_redshift_with_rescue() {

        use crate::redshift::IOP::oracle::coset_combining_rescue_tree::*;
        use crate::redshift::IOP::channel::rescue_channel::*;

        type E = Transparent252;
        type O = FriSpecificRescueTree<Fr>;
        type T = StatelessRescueChannel<Fr>;

        let res = test_redshift_template::<E, O, T>(
            Fr::one(),
            Fr::one(),
            1000,
            16,
            4,
            2,
            4);

        match res {
            Ok(valid) => assert_eq!(valid, true),
            Err(_) => println!("Some erro has been occured!"),
        };       
    }
}