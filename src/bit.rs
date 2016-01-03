use tinysnark::FieldT;

use super::variable::*;
use self::Bit::*;

#[derive(Clone)]
pub enum Bit {
    Constant(bool),
    Is(Var),
    Not(Var)
}

fn resolve_not(v: &Var) -> Var {
    gadget(&[v], 1, |i, o| {
        if *i[0] == FieldT::zero() {
            *o[0] = FieldT::one();
        } else {
            *o[0] = FieldT::zero();
        }
    }, |i, o, cs| {
        // (1 - a) * 1 = b
        cs.push(Constraint);

        vec![o[0]]
    }).remove(0)
}

impl Bit {
    pub fn val(&self, map: &[FieldT]) -> bool {
        match *self {
            Constant(c) => c,
            Not(ref v) => v.val(map) == FieldT::zero(),
            Is(ref v) => v.val(map) == FieldT::one()
        }
    }

    pub fn walk(&self, counter: &mut usize, constraints: &mut Vec<Constraint>, witness_map: &mut WitnessMap) {
        match *self {
            Constant(_) => {},
            Not(ref v) => {
                v.walk(counter, constraints, witness_map);
            },
            Is(ref v) => {
                v.walk(counter, constraints, witness_map);
            }
        }
    }

    pub fn new(v: &Var) -> Bit {
        Is(gadget(&[v], 0, |_, _| {}, |i, o, cs| {
            cs.push(Constraint);

            vec![i[0]]
        }).remove(0))
    }

    pub fn constant(num: bool) -> Bit {
        Constant(num)
    }

    // self xor other
    pub fn xor(&self, other: &Bit) -> Bit {
        match (self, other) {
            (&Constant(a), &Constant(b)) => {
                Constant(a != b)
            },
            (&Is(ref v), &Constant(a)) | (&Constant(a), &Is(ref v)) => {
                if a {
                    // Anything XOR 1 is the NOT of that thing.
                    Not(v.clone())
                } else {
                    // Anything XOR 0 equals that thing.
                    Is(v.clone())
                }
            },
            (&Is(ref a), &Is(ref b)) => {
                Is(gadget(&[a, b], 1, |i, o| {
                    if *i[0] != *i[1] {
                        *o[0] = FieldT::one();
                    } else {
                        *o[0] = FieldT::zero();
                    }
                }, |i, o, cs| {
                    // (2*b) * c = b+c - a
                    cs.push(Constraint);

                    vec![o[0]]
                }).remove(0))
            },
            (&Not(ref v), &Constant(a)) | (&Constant(a), &Not(ref v)) => {
                if a {
                    // Anything XOR 1 is the NOT of that thing.
                    // !A XOR 1 = A
                    Is(v.clone())
                } else {
                    Not(v.clone())
                }
            },
            (&Not(ref a), &Not(ref b)) => {
                // !A xor !B is equivalent to A xor B
                Is(a.clone()).xor(&Is(b.clone()))
            },
            (&Is(ref i), &Not(ref n)) | (&Not(ref n), &Is(ref i)) => {
                Is(i.clone()).xor(&Is(resolve_not(n)))
            }
        }
    }

    fn and(&self, other: &Bit) -> Bit {
        match (self, other) {
            (&Constant(a), &Constant(b)) => {
                Constant(a && b)
            },
            (&Constant(a), &Is(ref v)) | (&Is(ref v), &Constant(a)) => {
                if a {
                    Is(v.clone())
                } else {
                    Constant(false)
                }
            },
            (&Is(ref a), &Is(ref b)) => {
                Is(gadget(&[a, b], 1, |i, o| {
                    if *i[0] == FieldT::one() && *i[1] == FieldT::one() {
                        *o[0] = FieldT::one();
                    } else {
                        *o[0] = FieldT::zero();
                    }
                }, |i, o, cs| {
                    // a * b = c 
                    cs.push(Constraint);

                    vec![o[0]]
                }).remove(0))
            },
            (&Not(ref a), &Constant(c)) | (&Constant(c), &Not(ref a)) => {
                if c {
                    // X and 1 is the identity of X
                    Not(a.clone())
                } else {
                    Constant(false)
                }
            },
            (&Not(ref n), &Is(ref i)) | (&Is(ref i), &Not(ref n)) => {
                //Is(i.clone()).and(&Is(resolve_not(n)))
                Is(gadget(&[n, i], 1, |i, o| {
                    if *i[0] == FieldT::zero() && *i[1] == FieldT::one() {
                        *o[0] = FieldT::one();
                    } else {
                        *o[0] = FieldT::zero();
                    }
                }, |i, o, cs| {
                    // (1-a) * b = c
                    cs.push(Constraint);

                    vec![o[0]]
                }).remove(0))
            },
            (&Not(ref a), &Not(ref b)) => {
                //Is(resolve_not(a)).and(&Is(resolve_not(b)))
                Is(gadget(&[a, b], 1, |i, o| {
                    if *i[0] == FieldT::zero() && *i[1] == FieldT::zero() {
                        *o[0] = FieldT::one();
                    } else {
                        *o[0] = FieldT::zero();
                    }
                }, |i, o, cs| {
                    // (1 - a) * (1 - b) = c
                    cs.push(Constraint);

                    vec![o[0]]
                }).remove(0))
            }
        }
    }

    // (not self) and other
    pub fn notand(&self, other: &Bit) -> Bit {
        self.xor(&Constant(true)).and(other)
    }
}

#[cfg(test)]
fn test_binary_op<F: Fn(&Bit, &Bit) -> Bit>(op: F, a_in: i64, b_in: i64, c_out: i64)
{
    let a = Var::new(1);
    let b = Var::new(2);
    let a = Bit::new(&a);
    let b = Bit::new(&b);
    let mut counter = 3;
    let mut witness_map = WitnessMap::new();
    let mut constraints = vec![];

    let c = op(&a, &b);
    c.walk(&mut counter, &mut constraints, &mut witness_map);
    assert_eq!(counter, 4);
    assert_eq!(constraints.len(), 3);
    assert_eq!(witness_map.len(), 2);
    assert_eq!(witness_map[&1].len(), 2);
    assert_eq!(witness_map[&2].len(), 1);

    let mut f: Vec<FieldT> = (0..counter).map(|_| FieldT::zero()).collect();
    f[0] = FieldT::one();
    f[1] = FieldT::from(a_in);
    f[2] = FieldT::from(b_in);

    satisfy_field_elements(&mut f, &witness_map);

    assert_eq!(f[3], FieldT::from(c_out));
}

#[test]
fn test_xor() {
    use tinysnark;

    tinysnark::init();

    test_binary_op(Bit::xor, 0, 0, 0);
    test_binary_op(Bit::xor, 0, 1, 1);
    test_binary_op(Bit::xor, 1, 0, 1);
    test_binary_op(Bit::xor, 1, 1, 0);
}

#[test]
fn test_and() {
    use tinysnark;

    tinysnark::init();

    test_binary_op(Bit::and, 0, 0, 0);
    test_binary_op(Bit::and, 0, 1, 0);
    test_binary_op(Bit::and, 1, 0, 0);
    test_binary_op(Bit::and, 1, 1, 1);
}
