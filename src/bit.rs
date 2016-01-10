use tinysnark::FieldT;

use std::rc::Rc;
use std::cell::RefCell;
use super::variable::*;
use self::Bit::*;
use self::Op::*;

macro_rules! mirror {
    ($a:pat, $b:pat) => (($a, $b) | ($b, $a))
}

macro_rules! mirror_match {
    (@as_expr $e:expr) => {$e};

    (@parse
        $e:expr, ($($arms:tt)*);
        $(,)*
    ) => {
        mirror_match!(@as_expr match $e { $($arms)* })
    };

    (@parse
        $e:expr, $arms:tt;
        , $($tail:tt)*
    ) => {
        mirror_match!(@parse $e, $arms; $($tail)*)
    };

    (@parse
        $e:expr, ($($arms:tt)*);
        mirror!($a:pat, $b:pat) => $body:expr,
        $($tail:tt)*
    ) => {
        mirror_match!(
            @parse
            $e,
            (
                $($arms)*
                ($a, $b) | ($b, $a) => $body,
            );
            $($tail)*
        )
    };

    (@parse
        $e:expr, ($($arms:tt)*);
        $pat:pat => $body:expr,
        $($tail:tt)*
    ) => {
        mirror_match!(
            @parse
            $e,
            (
                $($arms)*
                $pat => $body,
            );
            $($tail)*
        )
    };

    (@parse
        $e:expr, ($($arms:tt)*);
        $pat:pat => $body:expr,
        $($tail:tt)*
    ) => {
        mirror_match!(
            @parse
            $e,
            (
                $($arms)*
                $pat => $body,
            );
            $($tail)*
        )
    };
    
    ($e:expr { $($arms:tt)* }) => {
        mirror_match!(@parse $e, (); $($arms)*)
    };
}

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
enum Op {
    And,
    Nand,

    Xor,
    Xnor,

    MaterialNonimplication,
    MaterialImplication,

    Nor,
    Or
}

impl Op {
    fn not(&self) -> Op {
        match *self {
            And => Nand,
            Nand => And,

            Xor => Xnor,
            Xnor => Xor,

            Nor => Or,
            Or => Nor,

            MaterialNonimplication => MaterialImplication,
            MaterialImplication => MaterialNonimplication
        }
    }

    fn val(&self, a: FieldT, b: FieldT) -> FieldT {
        let a = a == FieldT::one();
        let b = b == FieldT::one();
        let res = match *self {
            And => a && b,
            Nand => !(a && b),
            Xor => a != b,
            Xnor => a == b,
            Or => a || b,
            Nor => !(a || b),
            MaterialNonimplication => a && (!b),
            MaterialImplication => !(a && (!b))
        };

        if res {
            FieldT::one()
        } else {
            FieldT::zero()
        }
    }
}

#[derive(Clone)]
pub struct BinaryOp {
    a: Var,
    b: Var,
    op: Op,
    resolved: Rc<RefCell<Option<Var>>>
}

impl BinaryOp {
    fn new(a: Var, b: Var, op: Op) -> BinaryOp {
        BinaryOp {
            a: a,
            b: b,
            op: op,
            resolved: Rc::new(RefCell::new(None))
        }
    }

    fn walk(&self, counter: &mut usize, constraints: &mut Vec<Constraint>, witness_map: &mut WitnessMap)
    {
        self.a.walk(counter, constraints, witness_map);
        self.b.walk(counter, constraints, witness_map);
    }

    fn val(&self, map: &[FieldT], inverted: bool) -> FieldT {
        let v = self.op.val(self.a.val(map), self.b.val(map));

        if inverted {
            if v == FieldT::one() {
                FieldT::zero()
            } else {
                FieldT::one()
            }
        } else {
            v
        }
    }

    fn resolve(&self, inverted: bool) -> Bit {
        let res = { self.resolved.borrow_mut().clone() };

        match res {
            Some(v) => {
                if inverted {
                    Not(v)
                } else {
                    Is(v)
                }
            },
            None => {
                let v = resolve(&self.a, &self.b, self.op);

                *self.resolved.borrow_mut() = Some(v.clone());

                if inverted {
                    Not(v)
                } else {
                    Is(v)
                }
            }
        }
    }
}

#[derive(Clone)]
pub enum Bit {
    Constant(bool),
    Is(Var),
    Not(Var),
    Bin(BinaryOp, bool)
}

fn resolve(a: &Var, b: &Var, op: Op) -> Var {
    gadget(&[a, b], 1, move |vals| {
        let a = vals.get_input(0);
        let b = vals.get_input(1);

        vals.set_output(0, op.val(a, b));
    }, |i, o, cs| {
        cs.push(match op {
            And => Constraint::And(i[0].index(), i[1].index(), o[0].index()),
            Nand => Constraint::Nand(i[0].index(), i[1].index(), o[0].index()),
            Xor => Constraint::Xor(i[0].index(), i[1].index(), o[0].index()),
            Xnor => Constraint::Xnor(i[0].index(), i[1].index(), o[0].index()),
            Nor => Constraint::Nor(i[0].index(), i[1].index(), o[0].index()),
            Or => Constraint::Or(i[0].index(), i[1].index(), o[0].index()),
            MaterialNonimplication => Constraint::MaterialNonimplication(i[0].index(), i[1].index(), o[0].index()),
            MaterialImplication => Constraint::MaterialImplication(i[0].index(), i[1].index(), o[0].index())
        });

        vec![o[0]]
    }).remove(0)
}

impl Bit {
    pub fn val(&self, map: &[FieldT]) -> bool {
        match *self {
            Constant(c) => c,
            Not(ref v) => v.val(map) == FieldT::zero(),
            Is(ref v) => v.val(map) == FieldT::one(),
            Bin(ref bin, inverted) => bin.val(map, inverted) == FieldT::one()
        }
    }

    // probably could remove this
    pub fn resolve(&self) -> Bit {
        match *self {
            Bin(ref bin, inverted) => bin.resolve(inverted),
            _ => self.clone()
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
            },
            Bin(ref bin, _) => {
                bin.walk(counter, constraints, witness_map);
            }
        }
    }

    pub fn new(v: &Var) -> Bit {
        Is(gadget(&[v], 0, |_| {}, |i, o, cs| {
            cs.push(Constraint::Bitness(i[0].index()));

            vec![i[0]]
        }).remove(0))
    }

    pub fn constant(num: bool) -> Bit {
        Constant(num)
    }

    // self xor other
    pub fn xor(&self, other: &Bit) -> Bit {
        mirror_match!((self, other) {
            (&Constant(a), &Constant(b)) => {
                Constant(a != b)
            },
            mirror!(&Is(ref v), &Constant(a)) => {
                if a {
                    // Anything XOR 1 is the NOT of that thing.
                    Not(v.clone())
                } else {
                    // Anything XOR 0 equals that thing.
                    Is(v.clone())
                }
            },
            mirror!(&Not(ref v), &Constant(a)) => {
                if a {
                    // Anything XOR 1 is the NOT of that thing.
                    Is(v.clone())
                } else {
                    Not(v.clone())
                }
            },
            mirror!(&Bin(ref bin, inverted), &Constant(c)) => {
                if c {
                    // Anything XOR 1 is the NOT of that thing.
                    Bin(bin.clone(), !inverted)
                } else {
                    Bin(bin.clone(), inverted)
                }
            },
            mirror!(&Bin(ref bin, inverted), &Is(ref i)) => {
                bin.resolve(inverted).xor(&Is(i.clone()))
            },
            (&Bin(ref bin1, inverted1), &Bin(ref bin2, inverted2)) => {
                bin1.resolve(inverted1).xor(&bin2.resolve(inverted2))
            },
            mirror!(&Bin(ref bin, inverted), &Not(ref n)) => {
                bin.resolve(inverted).xor(&Not(n.clone()))
            },
            (&Not(ref a), &Not(ref b)) => {
                Bin(BinaryOp::new(a.clone(), b.clone(), Xor), false)
            },
            mirror!(&Is(ref i), &Not(ref n)) => {
                Bin(BinaryOp::new(i.clone(), n.clone(), Xnor), false)
            },
            (&Is(ref a), &Is(ref b)) => {
                Bin(BinaryOp::new(a.clone(), b.clone(), Xor), false)
            },
        })
    }

    pub fn and(&self, other: &Bit) -> Bit {
        mirror_match!((self, other) {
            (&Constant(a), &Constant(b)) => {
                Constant(a && b)
            },
            mirror!(&Is(ref v), &Constant(a)) => {
                if a {
                    // Anything AND 1 is the identity of that thing
                    Is(v.clone())
                } else {
                    // Anything AND 0 is false
                    Constant(false)
                }
            },
            mirror!(&Not(ref v), &Constant(a)) => {
                if a {
                    // Anything AND 1 is the identity of that thing
                    Not(v.clone())
                } else {
                    // Anything AND 0 is false
                    Constant(false)
                }
            },
            mirror!(&Bin(ref bin, inverted), &Constant(c)) => {
                if c {
                    // Anything AND 1 is the identity of that thing
                    Bin(bin.clone(), inverted)
                } else {
                    // Anything AND 0 is false
                    Constant(false)
                }
            },
            mirror!(&Bin(ref bin, inverted), &Is(ref i)) => {
                bin.resolve(inverted).and(&Is(i.clone()))
            },
            (&Bin(ref bin1, inverted1), &Bin(ref bin2, inverted2)) => {
                bin1.resolve(inverted1).and(&bin2.resolve(inverted2))
            },
            mirror!(&Bin(ref bin, inverted), &Not(ref n)) => {
                bin.resolve(inverted).and(&Not(n.clone()))
            },
            (&Not(ref a), &Not(ref b)) => {
                Bin(BinaryOp::new(a.clone(), b.clone(), Nor), false)
            },
            mirror!(&Is(ref i), &Not(ref n)) => {
                Bin(BinaryOp::new(i.clone(), n.clone(), MaterialNonimplication), false)
            },
            (&Is(ref a), &Is(ref b)) => {
                Bin(BinaryOp::new(a.clone(), b.clone(), And), false)
            },
        })
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
    let c = c.resolve();
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

    witness_field_elements(&mut f, &witness_map);

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
