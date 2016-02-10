use super::Bit;
use tinysnark::FieldT;
use super::super::variable::*;
use std::rc::Rc;

#[derive(Debug, Clone)]
enum Witness {
    And(Rc<Witness>, Rc<Witness>),
    Xor(Rc<Witness>, Rc<Witness>),
    Not(Rc<Witness>),
    Or(Rc<Witness>, Rc<Witness>),
    Cached(Rc<Witness>, usize),
    In(usize),
    Out(usize)
}

impl Witness {
    fn not(&self) -> Witness {
        Witness::Not(Rc::new(self.clone()))
    }

    fn eval(&self, vals: &mut VariableView) -> bool
    {
        match *self {
            Witness::And(ref a, ref b) => {
                a.eval(vals) && b.eval(vals)
            },
            Witness::Xor(ref a, ref b) => {
                a.eval(vals) ^ b.eval(vals)
            },
            Witness::Or(ref a, ref b) => {
                a.eval(vals) || b.eval(vals)
            },
            Witness::Not(ref a) => {
                !a.eval(vals)
            },
            Witness::Cached(ref a, cacheid) => {
                if vals.get_cache(cacheid).is_none() {
                    let v = a.eval(vals);
                    vals.set_cache(cacheid, v);
                }

                *vals.get_cache(cacheid).unwrap()
            },
            Witness::In(i) => {
                vals.get_input(i) == FieldT::one()
            },
            Witness::Out(i) => {
                // this shouldn't happen tbh?
                unreachable!()
            }
        }
    }
}

#[derive(Clone)]
enum Product {
    Boolean(Bit),
    Witness(Witness)
}

impl Product {
    fn witness(&self, allocator: &mut Allocator, e: usize) -> Product {
        match self {
            &Product::Boolean(Bit::Constant(b)) => Product::Boolean(Bit::Constant(b)),
            &Product::Boolean(ref b) => {
                // i guess we need to resolve it and make it an input but i don't know
                // what exponent we need to make it?
                let b = b.resolve();

                Product::Witness(allocator.input(&b, e))
            },
            &Product::Witness(ref w) => Product::Witness(Witness::Cached(Rc::new(w.clone()), allocator.cache()))
        }
    }

    fn or(&self, other: &Product, allocator: &mut Allocator, e: usize) -> Product {
        match (self.witness(allocator, e), other.witness(allocator, e)) {
            (Product::Boolean(a), Product::Boolean(b)) => {
                Product::Boolean(a.or(&b))
            },
            (Product::Boolean(Bit::Constant(b)), Product::Witness(ref w)) |
            (Product::Witness(ref w), Product::Boolean(Bit::Constant(b))) => {
                if b {
                    Product::Boolean(Bit::Constant(b))
                } else {
                    Product::Witness(w.clone())
                }
            },
            (Product::Witness(a), Product::Witness(b)) => {
                Product::Witness(Witness::Or(Rc::new(a.clone()), Rc::new(b.clone())))
            }
            (Product::Boolean(_), Product::Witness(_)) | (Product::Witness(_), Product::Boolean(_)) => {
                unreachable!()
            }
        }
    }
}

struct Allocator {
    lhs_terms: Vec<(FieldT, Witness)>,
    rhs_terms: Vec<(FieldT, Witness)>,
    witnesses: Vec<Witness>,
    inputs: Vec<Var>,
    outputs: usize,
    cache: usize
}

impl Allocator {
    fn cache(&mut self) -> usize {
        let i = self.cache;
        self.cache += 1;

        i
    }

    fn output(&mut self, w: &Witness, e: usize) -> Witness {
        let i = self.outputs;
        self.outputs += 1;

        self.rhs_terms.push((FieldT::from(2).exp(e), Witness::Out(i)));

        self.witnesses.push(w.clone());

        Witness::Out(i)
    }

    fn input(&mut self, bit: &Bit, e: usize) -> Witness {
        let bit = bit.resolve();
        match bit {
            Bit::Is(v) => {
                let i = self.inputs.len();

                self.inputs.push(v);

                self.lhs_terms.push((FieldT::from(2).exp(e), Witness::In(i)));

                Witness::In(i)
            },
            _ => unreachable!()
        }
    }
}

fn half_adder(e: usize, a: &Product, b: &Product, allocator: &mut Allocator) -> (Product, Product)
{
    match (a, b) {
        (&Product::Boolean(Bit::Constant(a)), &Product::Boolean(Bit::Constant(b))) => {
            (Product::Boolean(Bit::Constant(a && b)), Product::Boolean(Bit::Constant(a ^ b)))
        },
        (&Product::Boolean(Bit::Constant(c)), &Product::Boolean(ref x)) | (&Product::Boolean(ref x), &Product::Boolean(Bit::Constant(c))) => {
            if c {
                // If we add 1 to X, the carry is X and the sum is !X.
                (Product::Boolean(x.clone()), // carry
                 Product::Boolean(x.not())) // sum
            } else {
                // If we add 0 to X, the carry is 0 and the sum is X.
                (Product::Boolean(Bit::Constant(false)), // carry
                 Product::Boolean(x.clone())) // sum
            }
        },
        (&Product::Boolean(ref a), &Product::Boolean(ref b)) => {
            // In all other situations, a and b are both variables we must take as inputs
            // to the packing constraint.

            let a = allocator.input(a, e);
            let b = allocator.input(b, e);

            (Product::Witness(Witness::And(Rc::new(a.clone()), Rc::new(b.clone()))), // carry
             Product::Witness(Witness::Xor(Rc::new(a.clone()), Rc::new(b.clone())))) // sum
        },
        (&Product::Witness(ref w), &Product::Boolean(Bit::Constant(b))) |
        (&Product::Boolean(Bit::Constant(b)), &Product::Witness(ref w)) => {
            if b {
                (Product::Witness(w.clone()), Product::Witness(w.not()))
            } else {
                (Product::Boolean(Bit::Constant(false)), Product::Witness(w.clone()))
            }
        },
        (&Product::Witness(ref w), &Product::Boolean(ref b)) |
        (&Product::Boolean(ref b), &Product::Witness(ref w)) => {
            let b = allocator.input(b, e);

            (Product::Witness(Witness::And(Rc::new(w.clone()), Rc::new(b.clone()))), // carry
             Product::Witness(Witness::Xor(Rc::new(w.clone()), Rc::new(b.clone())))) // sum
        },
        (&Product::Witness(ref a), &Product::Witness(ref b)) => {
            (Product::Witness(Witness::And(Rc::new(a.clone()), Rc::new(b.clone()))), // carry
             Product::Witness(Witness::Xor(Rc::new(a.clone()), Rc::new(b.clone()))) // sum
            )
        }
    }
}

fn full_adder(e: usize, carry_in: &Product, a: &Bit, b: &Bit, allocator: &mut Allocator)
    -> (Product, Product)
{
    let (carry_first, sum_first) = half_adder(e, carry_in, &Product::Boolean(a.clone()), allocator);
    let (carry_second, sum_second) = half_adder(e, &sum_first, &Product::Boolean(b.clone()), allocator);

    let sum = match sum_second {
        Product::Boolean(b) => Product::Boolean(b),
        Product::Witness(w) => {
            Product::Witness(allocator.output(&w, e))
        }
    };

    (carry_first.or(&carry_second, allocator, e), sum)
}

pub fn add(a: &[Bit], b: &[Bit]) -> Vec<Bit> {
    assert_eq!(a.len(), b.len());
    assert!(a.len() < 100); // TODO: real capacity

    let mut carry = Product::Boolean(Bit::Constant(false));

    let mut allocator = Allocator {
        lhs_terms: vec![],
        rhs_terms: vec![],
        witnesses: vec![],
        inputs: vec![],
        outputs: 0,
        cache: 0
    };

    let outputs = a.chunks(8)
                   .flat_map(|c| c.into_iter())
                   .rev()
                   .zip(b.chunks(8).flat_map(|c| c.into_iter()).rev()).enumerate()
                   .map(|(e, (a, b))| {
                        let (new_carry, sum) = full_adder(e, &carry, a, b, &mut allocator);

                        carry = new_carry;

                        sum
                    }).collect::<Vec<_>>();

    // perform the last bit, even if we don't return it
    full_adder(a.len(), &carry, &Bit::Constant(false), &Bit::Constant(false), &mut allocator);

    let inputs = allocator.inputs;
    let new_outputs = if inputs.len() == 0 {
        vec![]
    } else {
        let witnesses = allocator.witnesses;

        gadget(&inputs, allocator.outputs, move |vals| {
            for (i, w) in witnesses.iter().enumerate() {
                let v = w.eval(vals);

                vals.set_output(i, if v {
                    FieldT::one()
                } else {
                    FieldT::zero()
                });
            }
        }, |i, o, cs| {
            // TODO!
            cs.push(Constraint(
                    vec![(FieldT::one(), Var::one())],
                    vec![(FieldT::one(), Var::one())],
                    vec![(FieldT::one(), Var::one())]
                ));

            o.into()
        })
    };

    outputs.into_iter().map(|p| {
        match p {
            Product::Witness(Witness::Out(o)) => Bit::new(&new_outputs[o]), // UNSAFE THERE'S NO BITNESS CONSTRAINT!
            Product::Boolean(b) => b,
            _ => unreachable!()
        }
    }).rev().collect()
}