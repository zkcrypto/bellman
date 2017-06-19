use curves::*;
use super::*;

pub struct ProvingKey<E: Engine> {
    a_inputs: Vec<<E::G1 as Curve<E>>::Affine>,
    b1_inputs: Vec<<E::G1 as Curve<E>>::Affine>,
    b2_inputs: Vec<<E::G2 as Curve<E>>::Affine>,
    a_aux: Vec<<E::G1 as Curve<E>>::Affine>,
    b1_aux: Vec<<E::G1 as Curve<E>>::Affine>,
    b2_aux: Vec<<E::G2 as Curve<E>>::Affine>,
    h: Vec<<E::G1 as Curve<E>>::Affine>,
    l: Vec<<E::G1 as Curve<E>>::Affine>,
    alpha_g1: <E::G1 as Curve<E>>::Affine,
    beta_g1: <E::G1 as Curve<E>>::Affine,
    beta_g2: <E::G2 as Curve<E>>::Affine,
    delta_g1: <E::G1 as Curve<E>>::Affine,
    delta_g2: <E::G2 as Curve<E>>::Affine
}

pub struct VerifyingKey<E: Engine> {
    alpha_g1: <E::G1 as Curve<E>>::Affine,
    beta_g2: <E::G2 as Curve<E>>::Affine,
    gamma_g2: <E::G2 as Curve<E>>::Affine,
    delta_g2: <E::G2 as Curve<E>>::Affine,
    ic: Vec<<E::G1 as Curve<E>>::Affine>
}

pub struct PreparedVerifyingKey<E: Engine> {
    alpha_g1_beta_g2: E::Fqk,
    neg_gamma_g2: <E::G2 as Curve<E>>::Prepared,
    neg_delta_g2: <E::G2 as Curve<E>>::Prepared,
    ic: Vec<<E::G1 as Curve<E>>::Affine>
}

pub struct Proof<E: Engine> {
    a: E::G1,
    b: E::G2,
    c: E::G1
}

pub fn keypair<E: Engine, C: Circuit<E>>(
    e: &E,
    circuit: C,
    tau: &E::Fr,
    alpha: &E::Fr,
    beta: &E::Fr,
    gamma: &E::Fr,
    delta: &E::Fr
) -> (ProvingKey<E>, VerifyingKey<E>)
{
    struct KeypairAssembly<E: Engine> {
        num_inputs: usize,
        num_aux: usize,
        num_constraints: usize,
        at_inputs: Vec<Vec<(E::Fr, usize)>>,
        bt_inputs: Vec<Vec<(E::Fr, usize)>>,
        ct_inputs: Vec<Vec<(E::Fr, usize)>>,
        at_aux: Vec<Vec<(E::Fr, usize)>>,
        bt_aux: Vec<Vec<(E::Fr, usize)>>,
        ct_aux: Vec<Vec<(E::Fr, usize)>>
    }

    impl<E: Engine> PublicConstraintSystem<E> for KeypairAssembly<E> {
        fn alloc_input(&mut self, _: E::Fr) -> Variable {
            let index = self.num_inputs;
            self.num_inputs += 1;

            self.at_inputs.push(vec![]);
            self.bt_inputs.push(vec![]);
            self.ct_inputs.push(vec![]);

            Variable(Index::Input(index))
        }
    }

    impl<E: Engine> ConstraintSystem<E> for KeypairAssembly<E> {
        fn alloc(&mut self, _: E::Fr) -> Variable {
            let index = self.num_aux;
            self.num_aux += 1;

            self.at_aux.push(vec![]);
            self.bt_aux.push(vec![]);
            self.ct_aux.push(vec![]);

            Variable(Index::Aux(index))
        }

        fn enforce(
            &mut self,
            a: LinearCombination<E>,
            b: LinearCombination<E>,
            c: LinearCombination<E>
        )
        {
            fn qap_eval<E: Engine>(
                l: LinearCombination<E>,
                inputs: &mut [Vec<(E::Fr, usize)>],
                aux: &mut [Vec<(E::Fr, usize)>],
                this_constraint: usize
            )
            {
                for (index, coeff) in l.0 {
                    match index {
                        Index::Input(id) => inputs[id].push((coeff, this_constraint)),
                        Index::Aux(id) => aux[id].push((coeff, this_constraint))
                    }
                }
            }

            qap_eval(a, &mut self.at_inputs, &mut self.at_aux, self.num_constraints);
            qap_eval(b, &mut self.bt_inputs, &mut self.bt_aux, self.num_constraints);
            qap_eval(c, &mut self.ct_inputs, &mut self.ct_aux, self.num_constraints);

            self.num_constraints += 1;
        }
    }

    let mut assembly = KeypairAssembly {
        num_inputs: 0,
        num_aux: 0,
        num_constraints: 0,
        at_inputs: vec![],
        bt_inputs: vec![],
        ct_inputs: vec![],
        at_aux: vec![],
        bt_aux: vec![],
        ct_aux: vec![]
    };

    assembly.alloc_input(E::Fr::one(e));

    circuit.synthesize(e, &mut assembly).synthesize(e, &mut assembly);

    // Input consistency constraints: x * 0 = 0
    for i in 0..assembly.num_inputs {
        assembly.enforce(LinearCombination::zero(e).add(E::Fr::one(e), Variable(Index::Input(i))),
                         LinearCombination::zero(e),
                         LinearCombination::zero(e));
    }

    let domain = domain::EvaluationDomain::new(e, assembly.num_constraints as u64);

    let mut u = Vec::with_capacity(domain.m as usize);
    {
        let mut acc = E::Fr::one(e);
        for _ in 0..domain.m {
            u.push(acc);
            acc.mul_assign(e, tau);
        }
    }

    let gamma_inverse = gamma.inverse(e).unwrap();
    let delta_inverse = delta.inverse(e).unwrap();

    let g1_table;
    let h;
    {
        let mut powers_of_tau = u.clone();
        powers_of_tau.truncate((domain.m - 1) as usize);

        let mut coeff = delta_inverse;
        coeff.mul_assign(e, &domain.z(e, tau));
        for h in &mut powers_of_tau {
            h.mul_assign(e, &coeff);
        }

        g1_table = E::G1::one(e).optimal_window_batch(e,
            (domain.m - 1) as usize + (assembly.num_inputs + assembly.num_aux) * 3
        );

        h = e.batch_baseexp(&g1_table, powers_of_tau);
    }

    domain.ifft(e, &mut u);

    fn eval<E: Engine>(
        e: &E,
        u: &[E::Fr],
        alpha: &E::Fr,
        beta: &E::Fr,
        inv: &E::Fr,
        at_in: Vec<Vec<(E::Fr, usize)>>,
        bt_in: Vec<Vec<(E::Fr, usize)>>,
        ct_in: Vec<Vec<(E::Fr, usize)>>
    ) -> (Vec<E::Fr>, Vec<E::Fr>, Vec<E::Fr>)
    {
        assert_eq!(at_in.len(), bt_in.len());
        assert_eq!(bt_in.len(), ct_in.len());

        fn eval_at_tau<E: Engine>(
            e: &E,
            val: Vec<(E::Fr, usize)>,
            u: &[E::Fr]
        ) -> E::Fr
        {
            let mut acc = E::Fr::zero();

            for (coeff, index) in val {
                let mut n = u[index];
                n.mul_assign(e, &coeff);
                acc.add_assign(e, &n);
            }

            acc
        }

        let mut a_out = Vec::with_capacity(at_in.len());
        let mut b_out = Vec::with_capacity(at_in.len());
        let mut l_out = Vec::with_capacity(at_in.len());

        for ((a, b), c) in at_in.into_iter().zip(bt_in.into_iter()).zip(ct_in.into_iter()) {
            let a = eval_at_tau(e, a, u);
            let b = eval_at_tau(e, b, u);

            let mut t0 = a;
            t0.mul_assign(e, beta);

            let mut t1 = b;
            t1.mul_assign(e, alpha);

            t0.add_assign(e, &t1);
            t0.add_assign(e, &eval_at_tau(e, c, u));
            t0.mul_assign(e, inv);

            a_out.push(a);
            b_out.push(b);
            l_out.push(t0);
        }

        (a_out, b_out, l_out)
    }

    let (a_inputs, b_inputs, ic_coeffs) = eval(e, &u, alpha, beta, &gamma_inverse, assembly.at_inputs, assembly.bt_inputs, assembly.ct_inputs);
    let a_inputs = e.batch_baseexp(&g1_table, a_inputs);
    let b1_inputs = e.batch_baseexp(&g1_table, &b_inputs);
    let ic_coeffs = e.batch_baseexp(&g1_table, ic_coeffs);
    let (a_aux, b_aux, l_coeffs) = eval(e, &u, alpha, beta, &delta_inverse, assembly.at_aux, assembly.bt_aux, assembly.ct_aux);
    let a_aux = e.batch_baseexp(&g1_table, a_aux);
    let b1_aux = e.batch_baseexp(&g1_table, &b_aux);
    let l_coeffs = e.batch_baseexp(&g1_table, l_coeffs);

    drop(g1_table);

    let g2_table = E::G2::one(e).optimal_window_batch(e,
        (assembly.num_inputs + assembly.num_aux)
    );

    let b2_inputs = e.batch_baseexp(&g2_table, b_inputs);
    let b2_aux = e.batch_baseexp(&g2_table, b_aux);

    let mut alpha_g1 = E::G1::one(e);
    alpha_g1.mul_assign(e, alpha);
    let mut beta_g1 = E::G1::one(e);
    beta_g1.mul_assign(e, beta);
    let mut beta_g2 = E::G2::one(e);
    beta_g2.mul_assign(e, beta);
    let mut gamma_g2 = E::G2::one(e);
    gamma_g2.mul_assign(e, gamma);
    let mut delta_g1 = E::G1::one(e);
    delta_g1.mul_assign(e, delta);
    let mut delta_g2 = E::G2::one(e);
    delta_g2.mul_assign(e, delta);

    (
        ProvingKey {
            a_inputs: a_inputs,
            b1_inputs: b1_inputs,
            b2_inputs: b2_inputs,
            a_aux: a_aux,
            b1_aux: b1_aux,
            b2_aux: b2_aux,
            h: h,
            l: l_coeffs,
            delta_g1: delta_g1.to_affine(e),
            delta_g2: delta_g2.to_affine(e),
            alpha_g1: alpha_g1.to_affine(e),
            beta_g1: beta_g1.to_affine(e),
            beta_g2: beta_g2.to_affine(e)
        },
        VerifyingKey {
            alpha_g1: alpha_g1.to_affine(e),
            beta_g2: beta_g2.to_affine(e),
            gamma_g2: gamma_g2.to_affine(e),
            delta_g2: delta_g2.to_affine(e),
            ic: ic_coeffs
        }
    )
}

pub fn prepare_verifying_key<E: Engine>(
    e: &E,
    vk: &VerifyingKey<E>
) -> PreparedVerifyingKey<E>
{
    let mut gamma = vk.gamma_g2;
    gamma.negate(e);
    let mut delta = vk.delta_g2;
    delta.negate(e);

    PreparedVerifyingKey {
        alpha_g1_beta_g2: e.pairing(&vk.alpha_g1, &vk.beta_g2),
        neg_gamma_g2: gamma.prepare(e),
        neg_delta_g2: delta.prepare(e),
        ic: vk.ic.clone()
    }
}

pub struct VerifierInput<'a, E: Engine + 'a> {
    e: &'a E,
    acc: E::G1,
    ic: &'a [<E::G1 as Curve<E>>::Affine],
    insufficient_inputs: bool,
    num_inputs: usize,
    num_aux: usize
}

impl<'a, E: Engine> ConstraintSystem<E> for VerifierInput<'a, E> {
    fn alloc(&mut self, _: E::Fr) -> Variable {
        let index = self.num_aux;
        self.num_aux += 1;

        Variable(Index::Aux(index))
    }

    fn enforce(
        &mut self,
        _: LinearCombination<E>,
        _: LinearCombination<E>,
        _: LinearCombination<E>
    )
    {
        // Do nothing; we don't care about the constraint system
        // in this context.
    }
}

pub fn verify<'a, E: Engine, C: Input<E>, F: FnOnce(&mut VerifierInput<'a, E>) -> C>(
    e: &'a E,
    circuit: F,
    proof: &Proof<E>,
    pvk: &'a PreparedVerifyingKey<E>
) -> bool
{
    struct InputAllocator<T>(T);

    impl<'a, 'b, E: Engine> PublicConstraintSystem<E> for InputAllocator<&'b mut VerifierInput<'a, E>> {
        fn alloc_input(&mut self, value: E::Fr) -> Variable {
            if self.0.ic.len() == 0 {
                self.0.insufficient_inputs = true;
            } else {
                self.0.acc.add_assign(self.0.e, &self.0.ic[0].mul(self.0.e, &value));
                self.0.ic = &self.0.ic[1..];
            }

            let index = self.0.num_inputs;
            self.0.num_inputs += 1;

            Variable(Index::Input(index))
        }
    }

    impl<'a, 'b, E: Engine> ConstraintSystem<E> for InputAllocator<&'b mut VerifierInput<'a, E>> {
        fn alloc(&mut self, num: E::Fr) -> Variable {
            self.0.alloc(num)
        }

        fn enforce(
            &mut self,
            a: LinearCombination<E>,
            b: LinearCombination<E>,
            c: LinearCombination<E>
        )
        {
            self.0.enforce(a, b, c);
        }
    }

    let mut witness = VerifierInput {
        e: e,
        acc: pvk.ic[0].to_jacobian(e),
        ic: &pvk.ic[1..],
        insufficient_inputs: false,
        num_inputs: 1,
        num_aux: 0
    };

    circuit(&mut witness).synthesize(e, &mut InputAllocator(&mut witness));

    if witness.ic.len() != 0 || witness.insufficient_inputs {
        return false;
    }

    e.final_exponentiation(
        &e.miller_loop([
            (&proof.a.prepare(e), &proof.b.prepare(e)),
            (&witness.acc.prepare(e), &pvk.neg_gamma_g2),
            (&proof.c.prepare(e), &pvk.neg_delta_g2)
        ].into_iter())
    ) == pvk.alpha_g1_beta_g2
}

pub fn prove<E: Engine, C: Circuit<E>>(
    e: &E,
    circuit: C,
    r: &E::Fr,
    s: &E::Fr,
    pk: &ProvingKey<E>
) -> Result<Proof<E>, ()>
{
    struct ProvingAssignment<'a, E: Engine + 'a> {
        e: &'a E,
        // Evaluations of A, B, C polynomials
        a: Vec<E::Fr>,
        b: Vec<E::Fr>,
        c: Vec<E::Fr>,
        // Assignments of variables
        input_assignment: Vec<E::Fr>,
        aux_assignment: Vec<E::Fr>
    }

    impl<'a, E: Engine> PublicConstraintSystem<E> for ProvingAssignment<'a, E> {
        fn alloc_input(&mut self, value: E::Fr) -> Variable {
            self.input_assignment.push(value);

            Variable(Index::Input(self.input_assignment.len() - 1))
        }
    }

    impl<'a, E: Engine> ConstraintSystem<E> for ProvingAssignment<'a, E> {
        fn alloc(&mut self, value: E::Fr) -> Variable {
            self.aux_assignment.push(value);

            Variable(Index::Aux(self.aux_assignment.len() - 1))
        }

        fn enforce(
            &mut self,
            a: LinearCombination<E>,
            b: LinearCombination<E>,
            c: LinearCombination<E>
        )
        {
            self.a.push(a.evaluate(self.e, &self.input_assignment, &self.aux_assignment));
            self.b.push(b.evaluate(self.e, &self.input_assignment, &self.aux_assignment));
            self.c.push(c.evaluate(self.e, &self.input_assignment, &self.aux_assignment));
        }
    }

    let mut prover = ProvingAssignment {
        e: e,
        a: vec![],
        b: vec![],
        c: vec![],
        input_assignment: vec![],
        aux_assignment: vec![]
    };

    prover.alloc_input(E::Fr::one(e));

    circuit.synthesize(e, &mut prover).synthesize(e, &mut prover);

    // Input consistency constraints: x * 0 = 0
    for i in 0..prover.input_assignment.len() {
        prover.enforce(LinearCombination::zero(e).add(E::Fr::one(e), Variable(Index::Input(i))),
                       LinearCombination::zero(e),
                       LinearCombination::zero(e));
    }

    // Perform FFTs
    let h = {
        let domain = domain::EvaluationDomain::new(e, prover.a.len() as u64);
        prover.a.resize(domain.m as usize, E::Fr::zero());
        prover.b.resize(domain.m as usize, E::Fr::zero());
        prover.c.resize(domain.m as usize, E::Fr::zero());
        domain.ifft(e, &mut prover.a);
        domain.coset_fft(e, &mut prover.a);
        domain.ifft(e, &mut prover.b);
        domain.coset_fft(e, &mut prover.b);
        domain.ifft(e, &mut prover.c);
        domain.coset_fft(e, &mut prover.c);

        let mut h = prover.a;
        domain.mul_assign(e, &mut h, prover.b);
        domain.sub_assign(e, &mut h, prover.c);
        domain.divide_by_z_on_coset(e, &mut h);
        domain.icoset_fft(e, &mut h);

        e.multiexp(&pk.h, &h[0..(domain.m-1) as usize])?
    };

    // Construct proof
    let mut g_a = pk.delta_g1.mul(e, r);
    g_a.add_assign(e, &pk.alpha_g1.to_jacobian(e));
    let mut g_b = pk.delta_g2.mul(e, s);
    g_b.add_assign(e, &pk.beta_g2.to_jacobian(e));
    let mut g_c;
    {
        let mut rs = *r;
        rs.mul_assign(e, s);
        g_c = pk.delta_g1.mul(e, &rs);
        g_c.add_assign(e, &pk.alpha_g1.mul(e, s));
        g_c.add_assign(e, &pk.beta_g1.mul(e, r));
    }
    let mut a_answer: E::G1 = e.multiexp(&pk.a_inputs, &prover.input_assignment)?;
    a_answer.add_assign(e, &e.multiexp(&pk.a_aux, &prover.aux_assignment)?);
    g_a.add_assign(e, &a_answer);
    a_answer.mul_assign(e, s);
    g_c.add_assign(e, &a_answer);
    let mut b1_answer: E::G1 = e.multiexp(&pk.b1_inputs, &prover.input_assignment)?;
    b1_answer.add_assign(e, &e.multiexp(&pk.b1_aux, &prover.aux_assignment)?);
    let mut b2_answer: E::G2 = e.multiexp(&pk.b2_inputs, &prover.input_assignment)?;
    b2_answer.add_assign(e, &e.multiexp(&pk.b2_aux, &prover.aux_assignment)?);
    g_b.add_assign(e, &b2_answer);
    b1_answer.mul_assign(e, r);
    g_c.add_assign(e, &b1_answer);
    g_c.add_assign(e, &h);
    g_c.add_assign(e, &e.multiexp(&pk.l, &prover.aux_assignment)?);

    Ok(Proof {
        a: g_a,
        b: g_b,
        c: g_c
    })
}

#[cfg(test)]
mod tests;
