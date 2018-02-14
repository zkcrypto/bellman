use pairing::{
    Engine,
    CurveAffine
};

use ::{
    SynthesisError
};

use multiexp::SourceBuilder;

use std::sync::Arc;

#[cfg(test)]
mod tests;

mod generator;
mod prover;
mod verifier;

pub use self::generator::*;
pub use self::prover::*;
pub use self::verifier::*;

#[derive(Clone)]
pub struct Proof<E: Engine> {
    a: E::G1Affine,
    b: E::G2Affine,
    c: E::G1Affine
}

#[derive(Clone)]
pub struct VerifyingKey<E: Engine> {
    // alpha in g1 for verifying and for creating A/C elements of
    // proof. Never the point at infinity.
    alpha_g1: E::G1Affine,

    // beta in g1 and g2 for verifying and for creating B/C elements
    // of proof. Never the point at infinity.
    beta_g1: E::G1Affine,
    beta_g2: E::G2Affine,

    // gamma in g2 for verifying. Never the point at infinity.
    gamma_g2: E::G2Affine,

    // delta in g1/g2 for verifying and proving, essentially the magic
    // trapdoor that forces the prover to evaluate the C element of the
    // proof with only components from the CRS. Never the point at
    // infinity.
    delta_g1: E::G1Affine,
    delta_g2: E::G2Affine,

    // Elements of the form (beta * u_i(tau) + alpha v_i(tau) + w_i(tau)) / gamma
    // for all public inputs. Because all public inputs have a "soundness
    // of input consistency" constraint, this is the same size as the
    // number of inputs, and never contains points at infinity.
    ic: Vec<E::G1Affine>
}

#[derive(Clone)]
pub struct Parameters<E: Engine> {
    pub vk: VerifyingKey<E>,

    // Elements of the form ((tau^i * t(tau)) / delta) for i between 0 and 
    // m-2 inclusive. Never contains points at infinity.
    h: Arc<Vec<E::G1Affine>>,

    // Elements of the form (beta * u_i(tau) + alpha v_i(tau) + w_i(tau)) / delta
    // for all auxillary inputs. Variables can never be unconstrained, so this
    // never contains points at infinity.
    l: Arc<Vec<E::G1Affine>>,

    // QAP "A" polynomials evaluated at tau in the Lagrange basis. Never contains
    // points at infinity: polynomials that evaluate to zero are omitted from
    // the CRS and the prover can deterministically skip their evaluation.
    a: Arc<Vec<E::G1Affine>>,

    // QAP "B" polynomials evaluated at tau in the Lagrange basis. Needed in
    // G1 and G2 for C/B queries, respectively. Never contains points at
    // infinity for the same reason as the "A" polynomials.
    b_g1: Arc<Vec<E::G1Affine>>,
    b_g2: Arc<Vec<E::G2Affine>>
}

pub struct PreparedVerifyingKey<E: Engine> {
    /// Pairing result of alpha*beta
    alpha_g1_beta_g2: E::Fqk,
    /// -gamma in G2
    neg_gamma_g2: <E::G2Affine as CurveAffine>::Prepared,
    /// -delta in G2
    neg_delta_g2: <E::G2Affine as CurveAffine>::Prepared,
    /// Copy of IC from `VerifiyingKey`.
    ic: Vec<E::G1Affine>
}

pub trait ParameterSource<E: Engine> {
    type G1Builder: SourceBuilder<E::G1Affine>;
    type G2Builder: SourceBuilder<E::G2Affine>;

    fn get_vk(
        &mut self,
        num_ic: usize
    ) -> Result<VerifyingKey<E>, SynthesisError>;
    fn get_h(
        &mut self,
        num_h: usize
    ) -> Result<Self::G1Builder, SynthesisError>;
    fn get_l(
        &mut self,
        num_l: usize
    ) -> Result<Self::G1Builder, SynthesisError>;
    fn get_a(
        &mut self,
        num_inputs: usize,
        num_aux: usize
    ) -> Result<(Self::G1Builder, Self::G1Builder), SynthesisError>;
    fn get_b_g1(
        &mut self,
        num_inputs: usize,
        num_aux: usize
    ) -> Result<(Self::G1Builder, Self::G1Builder), SynthesisError>;
    fn get_b_g2(
        &mut self,
        num_inputs: usize,
        num_aux: usize
    ) -> Result<(Self::G2Builder, Self::G2Builder), SynthesisError>;
}

impl<'a, E: Engine> ParameterSource<E> for &'a Parameters<E> {
    type G1Builder = (Arc<Vec<E::G1Affine>>, usize);
    type G2Builder = (Arc<Vec<E::G2Affine>>, usize);

    fn get_vk(
        &mut self,
        _: usize
    ) -> Result<VerifyingKey<E>, SynthesisError>
    {
        Ok(self.vk.clone())
    }

    fn get_h(
        &mut self,
        _: usize
    ) -> Result<Self::G1Builder, SynthesisError>
    {
        Ok((self.h.clone(), 0))
    }

    fn get_l(
        &mut self,
        _: usize
    ) -> Result<Self::G1Builder, SynthesisError>
    {
        Ok((self.l.clone(), 0))
    }

    fn get_a(
        &mut self,
        num_inputs: usize,
        _: usize
    ) -> Result<(Self::G1Builder, Self::G1Builder), SynthesisError>
    {
        Ok(((self.a.clone(), 0), (self.a.clone(), num_inputs)))
    }

    fn get_b_g1(
        &mut self,
        num_inputs: usize,
        _: usize
    ) -> Result<(Self::G1Builder, Self::G1Builder), SynthesisError>
    {
        Ok(((self.b_g1.clone(), 0), (self.b_g1.clone(), num_inputs)))
    }

    fn get_b_g2(
        &mut self,
        num_inputs: usize,
        _: usize
    ) -> Result<(Self::G2Builder, Self::G2Builder), SynthesisError>
    {
        Ok(((self.b_g2.clone(), 0), (self.b_g2.clone(), num_inputs)))
    }
}
