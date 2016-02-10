use tinysnark::{Proof, Keypair, FieldT, LinearTerm, ConstraintSystem};
use super::variable::{Var,Constraint,WitnessMap,witness_field_elements};
use super::bit::Bit;

pub trait ConstraintWalker: 'static {
    fn walk(&self,
            counter: &mut usize,
            constraints: &mut Vec<Constraint>,
            witness_map: &mut WitnessMap);
}

impl<C: ConstraintWalker> ConstraintWalker for Vec<C> {
    fn walk(&self,
            counter: &mut usize,
            constraints: &mut Vec<Constraint>,
            witness_map: &mut WitnessMap)
    {
        for i in self {
            i.walk(counter, constraints, witness_map);
        }
    }
}

pub trait Constrainable {
    type Result: ConstraintWalker;

    fn synthesize(&self, enforce: &Bit) -> Self::Result;
}

impl<C: Constrainable> Constrainable for Vec<C> {
    type Result = Vec<C::Result>;

    fn synthesize(&self, enforce: &Bit) -> Vec<C::Result> {
        self.iter().map(|a| a.synthesize(enforce)).collect()
    }
}

pub trait Equals<Rhs: ?Sized> {
    type Result: Constrainable;

    fn must_equal(&self, other: &Rhs) -> Self::Result;
}

impl<Lhs, Rhs> Equals<[Rhs]> for [Lhs] where Lhs: Equals<Rhs> {
    type Result = Vec<Lhs::Result>;

    fn must_equal(&self, other: &[Rhs]) -> Vec<Lhs::Result> {
        assert_eq!(self.len(), other.len());

        self.iter().zip(other.iter()).map(|(a, b)| a.must_equal(b)).collect()
    }
}

pub struct Circuit {
    public_inputs: usize,
    private_inputs: usize,
    aux_inputs: usize,
    num_constraints: usize,
    keypair: Keypair,
    witness_map: WitnessMap
}

impl Circuit {
    pub fn num_constraints(&self) -> usize {
        self.num_constraints
    }

    pub fn verify(&self, proof: &Proof, public: &[FieldT]) -> bool
    {
        proof.verify(&self.keypair, public)
    }

    pub fn prove(&self, public: &[FieldT], private: &[FieldT]) -> Result<Proof, ()>
    {
        assert_eq!(public.len(), self.public_inputs);
        assert_eq!(private.len(), self.private_inputs);

        let mut vars = Vec::new();
        vars.push(FieldT::one());
        vars.extend_from_slice(public);
        vars.extend_from_slice(private);

        for i in 0..self.aux_inputs {
            vars.push(FieldT::zero());
        }

        witness_field_elements(&mut vars, &self.witness_map);

        let primary = &vars[1..public.len()+1];
        let aux = &vars[1+public.len()..];

        if !self.keypair.is_satisfied(primary, aux) {
            return Err(())
        }

        Ok(Proof::new(&self.keypair, primary, aux))
    }
}

pub struct CircuitBuilder {
    public_inputs: usize,
    private_inputs: usize,
    constraints: Vec<Box<ConstraintWalker>>
}

impl CircuitBuilder {
    pub fn new(num_public: usize, num_private: usize) -> (Vec<Var>, Vec<Var>, CircuitBuilder) {
    	(
    		(0..num_public).map(|x| Var::new(1+x)).collect(),
    		(0..num_private).map(|x| Var::new(1+num_public+x)).collect(),
            CircuitBuilder {
                public_inputs: num_public,
                private_inputs: num_private,
                constraints: Vec::new()
            },
    	)
    }

    pub fn constrain<C: Constrainable>(&mut self, constraint: C) {
        self.constraints.push(Box::new(constraint.synthesize(&Bit::constant(true))));
    }

    pub fn finalize(self) -> Circuit {
    	let mut counter = 1 + self.public_inputs + self.private_inputs;
        let mut constraints = vec![];
        let mut witness_map = WitnessMap::new();

        for c in self.constraints.into_iter() {
            c.walk(&mut counter, &mut constraints, &mut witness_map);
        }

        let mut cs = ConstraintSystem::new(self.public_inputs, (counter - 1) - self.public_inputs);

        let num_constraints = constraints.len();

        for Constraint(a, b, c) in constraints {
            let a: Vec<_> = a.into_iter().map(|x| LinearTerm { coeff: x.0, index: x.1.index() }).collect();
            let b: Vec<_> = b.into_iter().map(|x| LinearTerm { coeff: x.0, index: x.1.index() }).collect();
            let c: Vec<_> = c.into_iter().map(|x| LinearTerm { coeff: x.0, index: x.1.index() }).collect();

            cs.add_constraint(&a, &b, &c);
        }

        let kp = Keypair::new(&cs);

        Circuit {
            public_inputs: self.public_inputs,
            private_inputs: self.private_inputs,
            num_constraints: num_constraints,
            aux_inputs: ((counter - 1) - self.public_inputs) - self.private_inputs,
            keypair: kp,
            witness_map: witness_map
        }
    }
}

