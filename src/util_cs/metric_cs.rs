use crate::{ConstraintSystem, Index, LinearCombination, SynthesisError, Variable};
use ff::{Field, PrimeField, ScalarEngine};
use paired::Engine;
use std::cmp::Ordering;
use std::collections::{BTreeMap, HashMap};

#[derive(Clone, Copy)]
struct OrderedVariable(Variable);

#[derive(Debug)]
enum NamedObject {
    Constraint(usize),
    Var(Variable),
    Namespace,
}

impl Eq for OrderedVariable {}
impl PartialEq for OrderedVariable {
    fn eq(&self, other: &OrderedVariable) -> bool {
        match (self.0.get_unchecked(), other.0.get_unchecked()) {
            (Index::Input(ref a), Index::Input(ref b)) => a == b,
            (Index::Aux(ref a), Index::Aux(ref b)) => a == b,
            _ => false,
        }
    }
}
impl PartialOrd for OrderedVariable {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for OrderedVariable {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.0.get_unchecked(), other.0.get_unchecked()) {
            (Index::Input(ref a), Index::Input(ref b)) => a.cmp(b),
            (Index::Aux(ref a), Index::Aux(ref b)) => a.cmp(b),
            (Index::Input(_), Index::Aux(_)) => Ordering::Less,
            (Index::Aux(_), Index::Input(_)) => Ordering::Greater,
        }
    }
}

pub struct MetricCS<E: Engine> {
    named_objects: HashMap<String, NamedObject>,
    current_namespace: Vec<String>,
    #[allow(clippy::type_complexity)]
    constraints: Vec<(
        LinearCombination<E>,
        LinearCombination<E>,
        LinearCombination<E>,
        String,
    )>,
    inputs: Vec<String>,
    aux: Vec<String>,
}

fn proc_lc<E: ScalarEngine>(terms: &LinearCombination<E>) -> BTreeMap<OrderedVariable, E::Fr> {
    let mut map = BTreeMap::new();
    for (&var, &coeff) in terms.iter() {
        map.entry(OrderedVariable(var))
            .or_insert_with(E::Fr::zero)
            .add_assign(&coeff);
    }

    // Remove terms that have a zero coefficient to normalize
    let mut to_remove = vec![];
    for (var, coeff) in map.iter() {
        if coeff.is_zero() {
            to_remove.push(var.clone())
        }
    }

    for var in to_remove {
        map.remove(&var);
    }

    map
}

impl<E: Engine> MetricCS<E> {
    pub fn new() -> Self {
        MetricCS::default()
    }

    pub fn num_constraints(&self) -> usize {
        self.constraints.len()
    }

    pub fn num_inputs(&self) -> usize {
        self.inputs.len()
    }

    pub fn pretty_print_list(&self) -> Vec<String> {
        let mut result = Vec::new();

        for input in &self.inputs {
            result.push(format!("INPUT {}", input));
        }
        for aux in &self.aux {
            result.push(format!("AUX {}", aux));
        }

        for &(ref _a, ref _b, ref _c, ref name) in &self.constraints {
            result.push(name.to_string());
        }

        result
    }

    pub fn pretty_print(&self) -> String {
        let mut s = String::new();

        for input in &self.inputs {
            s.push_str(&format!("INPUT {}\n", &input))
        }

        let negone = {
            let mut tmp = E::Fr::one();
            tmp.negate();
            tmp
        };

        let powers_of_two = (0..E::Fr::NUM_BITS)
            .map(|i| E::Fr::from_str("2").unwrap().pow(&[u64::from(i)]))
            .collect::<Vec<_>>();

        let pp = |s: &mut String, lc: &LinearCombination<E>| {
            s.push('(');
            let mut is_first = true;
            for (var, coeff) in proc_lc::<E>(&lc) {
                if coeff == negone {
                    s.push_str(" - ")
                } else if !is_first {
                    s.push_str(" + ")
                }
                is_first = false;

                if coeff != E::Fr::one() && coeff != negone {
                    for (i, x) in powers_of_two.iter().enumerate() {
                        if x == &coeff {
                            s.push_str(&format!("2^{} . ", i));
                            break;
                        }
                    }

                    s.push_str(&format!("{} . ", coeff))
                }

                match var.0.get_unchecked() {
                    Index::Input(i) => {
                        s.push_str(&format!("`I{}`", &self.inputs[i]));
                    }
                    Index::Aux(i) => {
                        s.push_str(&format!("`A{}`", &self.aux[i]));
                    }
                }
            }
            if is_first {
                // Nothing was visited, print 0.
                s.push('0');
            }
            s.push(')');
        };

        for &(ref a, ref b, ref c, ref name) in &self.constraints {
            s.push('\n');

            s.push_str(&format!("{}: ", name));
            pp(&mut s, a);
            s.push_str(" * ");
            pp(&mut s, b);
            s.push_str(" = ");
            pp(&mut s, c);
        }

        s.push('\n');

        s
    }

    fn set_named_obj(&mut self, path: String, to: NamedObject) {
        if self.named_objects.contains_key(&path) {
            panic!("tried to create object at existing path: {}", path);
        }

        self.named_objects.insert(path, to);
    }
}

impl<E: Engine> Default for MetricCS<E> {
    fn default() -> Self {
        let mut map = HashMap::new();
        map.insert("ONE".into(), NamedObject::Var(MetricCS::<E>::one()));
        MetricCS {
            named_objects: map,
            current_namespace: vec![],
            constraints: vec![],
            inputs: vec![String::from("ONE")],
            aux: vec![],
        }
    }
}

impl<E: Engine> ConstraintSystem<E> for MetricCS<E> {
    type Root = Self;

    fn alloc<F, A, AR>(&mut self, annotation: A, _f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        let path = compute_path(&self.current_namespace, &annotation().into());
        self.aux.push(path);

        Ok(Variable::new_unchecked(Index::Aux(self.aux.len() - 1)))
    }

    fn alloc_input<F, A, AR>(&mut self, annotation: A, _f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        let path = compute_path(&self.current_namespace, &annotation().into());
        self.inputs.push(path);

        Ok(Variable::new_unchecked(Index::Input(self.inputs.len() - 1)))
    }

    fn enforce<A, AR, LA, LB, LC>(&mut self, annotation: A, a: LA, b: LB, c: LC)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
        LA: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
        LB: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
        LC: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
    {
        let path = compute_path(&self.current_namespace, &annotation().into());
        let index = self.constraints.len();
        self.set_named_obj(path.clone(), NamedObject::Constraint(index));

        let a = a(LinearCombination::zero());
        let b = b(LinearCombination::zero());
        let c = c(LinearCombination::zero());

        self.constraints.push((a, b, c, path));
    }

    fn push_namespace<NR, N>(&mut self, name_fn: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        let name = name_fn().into();
        let path = compute_path(&self.current_namespace, &name);
        self.set_named_obj(path, NamedObject::Namespace);
        self.current_namespace.push(name);
    }

    fn pop_namespace(&mut self) {
        assert!(self.current_namespace.pop().is_some());
    }

    fn get_root(&mut self) -> &mut Self::Root {
        self
    }
}

fn compute_path(ns: &[String], this: &str) -> String {
    if this.chars().any(|a| a == '/') {
        panic!("'/' is not allowed in names");
    }

    let mut name = String::new();

    let mut needs_separation = false;
    for ns in ns.iter().chain(Some(this.to_string()).iter()) {
        if needs_separation {
            name += "/";
        }

        name += ns;
        needs_separation = true;
    }

    name
}
