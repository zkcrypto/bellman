use crate::pairing::{
    Engine,
    CurveProjective
};

use crate::pairing::ff::{
    Field, 
    PrimeField
};

use super::{
    SynthesisError
};

pub trait Group<E: Engine>: Sized + Copy + Clone + Send + Sync {
    fn group_zero() -> Self;
    fn group_mul_assign(&mut self, by: &E::Fr);
    fn group_add_assign(&mut self, other: &Self);
    fn group_sub_assign(&mut self, other: &Self);
}

pub struct Point<G: CurveProjective>(pub G);

impl<G: CurveProjective> PartialEq for Point<G> {
    fn eq(&self, other: &Point<G>) -> bool {
        self.0 == other.0
    }
}

impl<G: CurveProjective> Copy for Point<G> { }

impl<G: CurveProjective> Clone for Point<G> {
    fn clone(&self) -> Point<G> {
        *self
    }
}

impl<G: CurveProjective> Group<G::Engine> for Point<G> {
    fn group_zero() -> Self {
        Point(G::zero())
    }
    fn group_mul_assign(&mut self, by: &G::Scalar) {
        self.0.mul_assign(by.into_repr());
    }
    fn group_add_assign(&mut self, other: &Self) {
        self.0.add_assign(&other.0);
    }
    fn group_sub_assign(&mut self, other: &Self) {
        self.0.sub_assign(&other.0);
    }
}

pub struct Scalar<E: Engine>(pub E::Fr);

impl<E: Engine> PartialEq for Scalar<E> {
    fn eq(&self, other: &Scalar<E>) -> bool {
        self.0 == other.0
    }
}

impl<E: Engine> Copy for Scalar<E> { }

impl<E: Engine> Clone for Scalar<E> {
    fn clone(&self) -> Scalar<E> {
        *self
    }
}

impl<E: Engine> Group<E> for Scalar<E> {
    fn group_zero() -> Self {
        Scalar(E::Fr::zero())
    }
    fn group_mul_assign(&mut self, by: &E::Fr) {
        self.0.mul_assign(by);
    }
    fn group_add_assign(&mut self, other: &Self) {
        self.0.add_assign(&other.0);
    }
    fn group_sub_assign(&mut self, other: &Self) {
        self.0.sub_assign(&other.0);
    }
}