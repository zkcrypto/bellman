use crate::pairing::ff::{Field, PrimeField};
use crate::pairing::{Engine};

use crate::{SynthesisError};
use std::marker::PhantomData;
use super::cs::*;
use crate::multicore::*;

use crate::plonk::polynomials::*;
use crate::plonk::domains::*;
use crate::plonk::fft::cooley_tukey_ntt::CTPrecomputations;
use crate::plonk::commitments::transcript::*;
use crate::plonk::commitments::transparent::iop_compiler::coset_combining_blake2s_tree::*;
use crate::plonk::commitments::transparent::iop_compiler::*;
use crate::plonk::transparent_engine::PartialTwoBitReductionField;

use super::gates::*;
use super::data_structures::*;
use super::utils::*;

#[derive(Debug)]
struct GeneratorAssembly<E: Engine> {
    m: usize,
    n: usize,
    input_gates: Vec<Gate<E::Fr>>,
    aux_gates: Vec<Gate<E::Fr>>,

    num_inputs: usize,
    num_aux: usize,

    is_finalized: bool,
}

impl<E: Engine> ConstraintSystem<E> for GeneratorAssembly<E> {
    // allocate a variable
    fn alloc<F>(&mut self, _value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError> 
    {
        self.num_aux += 1;
        let index = self.num_aux;

        Ok(Variable(Index::Aux(index)))
    }

    // allocate an input variable
    fn alloc_input<F>(&mut self, _value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError> 
    {
        self.num_inputs += 1;
        let index = self.num_inputs;
        let input_var = Variable(Index::Input(index));
        let zero = E::Fr::zero();
        let gate_coeffs = (E::Fr::one(), zero, zero, zero, zero, zero);
        let dummy = self.get_dummy_variable();
        let gate = Gate::<E::Fr>::new_gate((input_var, dummy, dummy), gate_coeffs);
        self.input_gates.push(gate);
        Ok(input_var)
    }

    // allocate an abstract gate
    fn new_gate(&mut self, variables: (Variable, Variable, Variable), 
        coeffs:(E::Fr, E::Fr, E::Fr, E::Fr, E::Fr, E::Fr)) -> Result<(), SynthesisError>
    {
        let gate = Gate::<E::Fr>::new_gate(variables, coeffs);
        self.aux_gates.push(gate);
        self.n += 1;

        Ok(())
    }

    fn get_dummy_variable(&self) -> Variable {
        self.dummy_variable()
    }
}

impl<E: Engine> GeneratorAssembly<E> {
    fn new_empty_gate(&mut self) -> usize {
        self.n += 1;
        let index = self.n;

        self.aux_gates.push(Gate::<E::Fr>::empty());

        index
    }

    fn set_gate(&mut self, gate: Gate<E::Fr>, index: usize) {
        self.aux_gates[index-1] = gate;
    }

    // allocate a constant
    fn enforce_constant(&mut self, variable: Variable, constant: E::Fr) -> Result<(), SynthesisError>
    {
        let gate = Gate::<E::Fr>::new_enforce_constant_gate(variable, Some(constant), self.dummy_variable());
        self.aux_gates.push(gate);
        self.n += 1;

        Ok(())
    }

    pub(crate) fn new() -> Self {
        let mut tmp = Self {
            n: 0,
            m: 0,
            input_gates: vec![],
            aux_gates: vec![],

            num_inputs: 0,
            num_aux: 0,

            is_finalized: false,
        };

        let zero = tmp.alloc(|| Ok(E::Fr::zero())).expect("should have no issues");
        tmp.enforce_constant(zero, E::Fr::zero()).expect("should have no issues");

        let one = tmp.alloc(|| Ok(E::Fr::one())).expect("should have no issues");
        tmp.enforce_constant(one, E::Fr::one()).expect("should have no issues");

        match (tmp.dummy_variable(), zero) {
            (Variable(Index::Aux(1)), Variable(Index::Aux(1))) => {},
            _ => panic!("zero variable is incorrect")
        }

        tmp
    }

    // return variable that is not in a constraint formally, but has some value
    fn dummy_variable(&self) -> Variable {
        // <Self as ConstraintSystem<E>>::ZERO
        Variable(Index::Aux(1))
    }
   
    pub(crate) fn num_gates(&self) -> usize {
        self.input_gates.len() + self.aux_gates.len()
    }
   
    fn finalize(&mut self) {
        if !self.is_finalized {
            let n = self.input_gates.len() + self.aux_gates.len();
            if !(n+1).is_power_of_two() {
                let empty_gate = Gate::<E::Fr>::new_empty_gate(self.dummy_variable());
                let new_aux_len = (n+1).next_power_of_two() - 1 - self.input_gates.len();
                self.aux_gates.resize(new_aux_len, empty_gate);
                let n = self.input_gates.len() + self.aux_gates.len();
                assert!((n+1).is_power_of_two());
            }       
            self.is_finalized = true;
        }     
    }

    fn get_data(&self) -> (&Vec<Gate<E::Fr>>, &Vec<Gate<E::Fr>>, &usize, &usize) {
        (&self.input_gates, &self.aux_gates, &self.num_inputs, &self.num_aux)
    }
}

pub fn setup_with_precomputations<E: Engine, C: Circuit<E>, CP: CTPrecomputations<E::Fr>, T: Transcript<E::Fr, 
    Input = <FriSpecificBlake2sTree<E::Fr> as IopInstance<E::Fr>> :: Commitment> >(
    circuit: &C,
    params: &RedshiftParameters<E::Fr>,
    omegas_bitreversed: &CP,
    ) -> Result<(RedshiftSetup<E::Fr, FriSpecificBlake2sTree<E::Fr>>, RedshiftSetupPrecomputation<E::Fr, FriSpecificBlake2sTree<E::Fr>>), SynthesisError> 
        where E::Fr : PartialTwoBitReductionField 
{
    let mut assembly = GeneratorAssembly::<E>::new();
    circuit.synthesize(&mut assembly)?;
    
    assembly.finalize();
    let (input_gates, aux_gates, num_inputs, num_aux) = assembly.get_data();
    let n = input_gates.len() + aux_gates.len();
    
    let worker = Worker::new();

    let mut transcript = T::new();

    let (q_l, q_r, q_o, q_m, q_c, q_add_sel, s_id, sigma_1, sigma_2, sigma_3) = 
        output_setup_polynomials::<E>(input_gates, aux_gates, num_inputs, num_aux, &worker)?;

    let q_l_commitment_data = commit_single_poly::<E, CP>(&q_l, omegas_bitreversed, &params, &worker)?;
    let q_r_commitment_data = commit_single_poly::<E, CP>(&q_r, omegas_bitreversed, &params, &worker)?;
    let q_o_commitment_data = commit_single_poly::<E, CP>(&q_o, omegas_bitreversed, &params, &worker)?;
    let q_m_commitment_data = commit_single_poly::<E, CP>(&q_m, omegas_bitreversed, &params, &worker)?;
    let q_c_commitment_data = commit_single_poly::<E, CP>(&q_c, omegas_bitreversed, &params, &worker)?;
    let q_add_sel_commitment_data = commit_single_poly::<E, CP>(&q_add_sel, omegas_bitreversed, &params, &worker)?;
    let s_id_commitment_data = commit_single_poly::<E, CP>(&s_id, omegas_bitreversed, &params, &worker)?;
    let sigma_1_commitment_data = commit_single_poly::<E, CP>(&sigma_1, omegas_bitreversed, &params, &worker)?;
    let sigma_2_commitment_data = commit_single_poly::<E, CP>(&sigma_2, omegas_bitreversed, &params, &worker)?;
    let sigma_3_commitment_data = commit_single_poly::<E, CP>(&sigma_3, omegas_bitreversed, &params, &worker)?;

    transcript.commit_input(&q_l_commitment_data.oracle.get_commitment());
    transcript.commit_input(&q_r_commitment_data.oracle.get_commitment());
    transcript.commit_input(&q_o_commitment_data.oracle.get_commitment());
    transcript.commit_input(&q_m_commitment_data.oracle.get_commitment());
    transcript.commit_input(&q_c_commitment_data.oracle.get_commitment());
    transcript.commit_input(&q_add_sel_commitment_data.oracle.get_commitment());
    transcript.commit_input(&s_id_commitment_data.oracle.get_commitment());
    transcript.commit_input(&sigma_1_commitment_data.oracle.get_commitment());
    transcript.commit_input(&sigma_2_commitment_data.oracle.get_commitment());
    transcript.commit_input(&sigma_3_commitment_data.oracle.get_commitment());

    let setup_point = transcript.get_challenge();

    let q_l_setup_value = q_l.evaluate_at(&worker, setup_point);
    let q_r_setup_value = q_r.evaluate_at(&worker, setup_point);
    let q_o_setup_value = q_o.evaluate_at(&worker, setup_point);
    let q_m_setup_value = q_m.evaluate_at(&worker, setup_point);
    let q_c_setup_value = q_c.evaluate_at(&worker, setup_point);
    let q_add_sel_setup_value = q_add_sel.evaluate_at(&worker, setup_point);

    let s_id_setup_value = s_id.evaluate_at(&worker, setup_point);
    let sigma_1_setup_value = sigma_1.evaluate_at(&worker, setup_point);
    let sigma_2_setup_value = sigma_2.evaluate_at(&worker, setup_point);
    let sigma_3_setup_value = sigma_3.evaluate_at(&worker, setup_point);

    let setup = RedshiftSetup::<E::Fr, FriSpecificBlake2sTree<E::Fr>> {
        n: n,
        q_l: q_l_commitment_data.oracle.get_commitment(),
        q_r: q_r_commitment_data.oracle.get_commitment(),
        q_o: q_o_commitment_data.oracle.get_commitment(),
        q_m: q_m_commitment_data.oracle.get_commitment(),
        q_c: q_c_commitment_data.oracle.get_commitment(),
        q_add_sel: q_add_sel_commitment_data.oracle.get_commitment(),
        s_id: s_id_commitment_data.oracle.get_commitment(),
        sigma_1: sigma_1_commitment_data.oracle.get_commitment(),
        sigma_2: sigma_2_commitment_data.oracle.get_commitment(),
        sigma_3: sigma_3_commitment_data.oracle.get_commitment(),
    };

    let precomputation = RedshiftSetupPrecomputation::<E::Fr, FriSpecificBlake2sTree<E::Fr>> {
        q_l_aux: SinglePolySetupData::<E::Fr, FriSpecificBlake2sTree<E::Fr>> {
            poly: q_l_commitment_data.poly,
            oracle: q_l_commitment_data.oracle,
            setup_point: setup_point,
            setup_value: q_l_setup_value,
        },
        q_r_aux: SinglePolySetupData::<E::Fr, FriSpecificBlake2sTree<E::Fr>> {
            poly: q_r_commitment_data.poly,
            oracle: q_r_commitment_data.oracle,
            setup_point: setup_point,
            setup_value: q_r_setup_value,
        },
        q_o_aux: SinglePolySetupData::<E::Fr, FriSpecificBlake2sTree<E::Fr>> {
            poly: q_o_commitment_data.poly,
            oracle: q_o_commitment_data.oracle,
            setup_point: setup_point,
            setup_value: q_o_setup_value,
        },
        q_m_aux: SinglePolySetupData::<E::Fr, FriSpecificBlake2sTree<E::Fr>> {
            poly: q_m_commitment_data.poly,
            oracle: q_m_commitment_data.oracle,
            setup_point: setup_point,
            setup_value: q_m_setup_value,
        },
        q_c_aux: SinglePolySetupData::<E::Fr, FriSpecificBlake2sTree<E::Fr>> {
            poly: q_c_commitment_data.poly,
            oracle: q_c_commitment_data.oracle,
            setup_point: setup_point,
            setup_value: q_c_setup_value,
        },
        q_add_sel_aux: SinglePolySetupData::<E::Fr, FriSpecificBlake2sTree<E::Fr>> {
            poly: q_add_sel_commitment_data.poly,
            oracle: q_add_sel_commitment_data.oracle,
            setup_point: setup_point,
            setup_value: q_add_sel_setup_value,
        },
        s_id_aux: SinglePolySetupData::<E::Fr, FriSpecificBlake2sTree<E::Fr>> {
            poly: s_id_commitment_data.poly,
            oracle: s_id_commitment_data.oracle,
            setup_point: setup_point,
            setup_value: s_id_setup_value,
        },
        sigma_1_aux: SinglePolySetupData::<E::Fr, FriSpecificBlake2sTree<E::Fr>> {
            poly: sigma_1_commitment_data.poly,
            oracle: sigma_1_commitment_data.oracle,
            setup_point: setup_point,
            setup_value: sigma_1_setup_value,
        },
        sigma_2_aux: SinglePolySetupData::<E::Fr, FriSpecificBlake2sTree<E::Fr>> {
            poly: sigma_2_commitment_data.poly,
            oracle: sigma_2_commitment_data.oracle,
            setup_point: setup_point,
            setup_value: sigma_2_setup_value,
        },
        sigma_3_aux: SinglePolySetupData::<E::Fr, FriSpecificBlake2sTree<E::Fr>> {
            poly: sigma_3_commitment_data.poly,
            oracle: sigma_3_commitment_data.oracle,
            setup_point: setup_point,
            setup_value: sigma_3_setup_value,
        },
    };

    Ok((setup, precomputation))
}