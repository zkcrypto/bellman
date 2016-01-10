use tinysnark::FieldT;
use std::cell::Cell;
use std::rc::Rc;
use std::fmt;
use std::collections::BTreeMap;

pub type WitnessMap = BTreeMap<usize, Vec<(Vec<usize>, Vec<usize>, Rc<Fn(&mut VariableView) + 'static>)>>;

struct VariableView<'a> {
    vars: &'a mut [FieldT],
    inputs: &'a [usize],
    outputs: &'a [usize]
}

impl<'a> VariableView<'a> {
    /// Sets an output variable at `index` to value `to`.
    pub fn set_output(&mut self, index: usize, to: FieldT) {
        self.vars[self.outputs[index]] = to;
    }

    /// Gets the value of an input variable at `index`.
    pub fn get_input(&self, index: usize) -> FieldT {
        self.vars[self.inputs[index]]
    }
}

use std::collections::Bound::Unbounded;

pub fn witness_field_elements(vars: &mut [FieldT], witness_map: &WitnessMap) {
    for (n, group) in witness_map.range(Unbounded, Unbounded) {
        for &(ref i, ref o, ref f) in group.iter() {
            let mut vars = VariableView {
                vars: vars,
                inputs: &*i,
                outputs: &*o
            };

            f(&mut vars);
        }
    }
}

#[derive(Clone)]
pub enum Constraint {
    Bitness(Rc<Cell<usize>>),
    And(Rc<Cell<usize>>, Rc<Cell<usize>>, Rc<Cell<usize>>),
    Nand(Rc<Cell<usize>>, Rc<Cell<usize>>, Rc<Cell<usize>>),
    Xor(Rc<Cell<usize>>, Rc<Cell<usize>>, Rc<Cell<usize>>),
    Xnor(Rc<Cell<usize>>, Rc<Cell<usize>>, Rc<Cell<usize>>),
    MaterialNonimplication(Rc<Cell<usize>>, Rc<Cell<usize>>, Rc<Cell<usize>>),
    MaterialImplication(Rc<Cell<usize>>, Rc<Cell<usize>>, Rc<Cell<usize>>),
    Nor(Rc<Cell<usize>>, Rc<Cell<usize>>, Rc<Cell<usize>>),
    Or(Rc<Cell<usize>>, Rc<Cell<usize>>, Rc<Cell<usize>>)
}

impl fmt::Debug for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", match *self {
            Constraint::Bitness(ref b) => format!("bitness: {}", b.get()),
            Constraint::And(ref a, ref b, ref c) => format!("{} = {} AND {}", c.get(), a.get(), b.get()),
            Constraint::Nand(ref a, ref b, ref c) => format!("{} = {} NAND {}", c.get(), a.get(), b.get()),
            Constraint::Xor(ref a, ref b, ref c) => format!("{} = {} XOR {}", c.get(), a.get(), b.get()),
            Constraint::Xnor(ref a, ref b, ref c) => format!("{} = {} XNOR {}", c.get(), a.get(), b.get()),
            Constraint::MaterialNonimplication(ref a, ref b, ref c) => format!("{} = {} ↛ {}", c.get(), a.get(), b.get()),
            Constraint::MaterialImplication(ref a, ref b, ref c) => format!("{} = {} <-> {}", c.get(), a.get(), b.get()),
            Constraint::Nor(ref a, ref b, ref c) => format!("{} = {} NOR {}", c.get(), a.get(), b.get()),
            Constraint::Or(ref a, ref b, ref c) => format!("{} = {} OR {}", c.get(), a.get(), b.get())
        })
    }
}

struct Gadget {
    inputs: Vec<Var>,
    aux: Vec<Var>,
    witness: Rc<Fn(&mut VariableView) + 'static>,
    constraints: Vec<Constraint>,
    group: usize,
    visited: Cell<bool>
}

impl Gadget {
    pub fn walk(&self, counter: &mut usize, constraints: &mut Vec<Constraint>, witness_map: &mut WitnessMap) {
        if self.visited.get() {
            return;
        }

        self.visited.set(true);

        for a in &self.aux {
            assert!(a.index.get() == 0);
            a.index.set(*counter);
            *counter += 1;
        }

        constraints.extend_from_slice(&self.constraints);

        for i in &self.inputs {
            i.walk(counter, constraints, witness_map);
        }

        let input_indexes = self.inputs.iter().map(|i| i.index.get()).collect();
        let output_indexes = self.aux.iter().map(|i| i.index.get()).collect();

        witness_map.entry(self.group)
                   .or_insert_with(|| Vec::new())
                   .push((input_indexes, output_indexes, self.witness.clone()));
    }
}

#[derive(Clone)]
pub struct Var {
    index: Rc<Cell<usize>>,
    gadget: Option<Rc<Gadget>>
}

impl Var {
    // todo: make this not public
    pub fn new(i: usize) -> Var {
        Var {
            index: Rc::new(Cell::new(i)),
            gadget: None
        }
    }

    // make this not public or unsafe too
    pub fn index(&self) -> Rc<Cell<usize>> {
        self.index.clone()
    }

    pub fn val(&self, map: &[FieldT]) -> FieldT {
        let index = self.index.get();
        assert!(index != 0);
        map[index]
    }

    fn group(&self) -> usize {
        match self.gadget {
            None => 0,
            Some(ref g) => g.group
        }
    }

    pub fn walk(&self, counter: &mut usize, constraints: &mut Vec<Constraint>, witness_map: &mut WitnessMap) {
        match self.gadget {
            None => {},
            Some(ref g) => g.walk(counter, constraints, witness_map)
        }
    }
}

pub fn gadget<W, C>(
    inputs: &[&Var],
    aux: usize,
    witness: W,
    constrain: C
) -> Vec<Var>
    where C: for<'a> Fn(&[&'a Var], &[&'a Var], &mut Vec<Constraint>) -> Vec<&'a Var>,
          W: Fn(&mut VariableView) + 'static
{
    let this_group = inputs.iter().map(|i| i.group()).max().map(|a| a+1).unwrap_or(0);

    let aux: Vec<_> = (0..aux).map(|_| Var::new(0)).collect();
    let aux: Vec<_> = aux.iter().collect();

    let mut constraints = vec![];

    let outputs = constrain(inputs, &*aux, &mut constraints);

    let gadget = Rc::new(Gadget {
        inputs: inputs.iter().map(|a| (*a).clone()).collect(),
        aux: aux.iter().map(|a| (*a).clone()).collect(),
        witness: Rc::new(witness),
        constraints: constraints,
        group: this_group,
        visited: Cell::new(false)
    });

    outputs.into_iter().map(|a| {
        let mut a = (*a).clone();

        // TODO: we should augment the gadget instead
        // of replacing it
        debug_assert!(a.gadget.is_none());

        a.gadget = Some(gadget.clone());
        a
    }).collect()
}
