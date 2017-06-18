macro_rules! curve_impl {
    (
        $engine:ident,
        $name:ident,
        $name_affine:ident,
        $name_prepared:ident,
        $name_uncompressed:ident,
        $params_name:ident,
        $params_field:ident,
        $basefield:ident,
        $scalarfield:ident
    ) => {
        #[repr(C)]
        #[derive(Copy, Clone, PartialEq, Eq, Debug)]
        pub struct $name_affine {
            x: $basefield,
            y: $basefield,
            infinity: bool
        }

        #[repr(C)]
        #[derive(Copy, Clone, Debug)]
        pub struct $name {
            x: $basefield,
            y: $basefield,
            z: $basefield
        }

        #[derive(Clone)]
        struct $params_name {
            zero: $name,
            one: $name,
            coeff_b: $basefield,
            windows: Vec<usize>,
            batch_windows: (usize, Vec<usize>)
        }

        impl Convert<$name_affine, $engine> for $name {
            type Target = $name_affine;

            fn convert(&self, engine: &$engine) -> Cow<$name_affine> {
                Cow::Owned(self.to_affine(engine))
            }
        }

        impl Group<$engine> for $name {
            fn group_zero(e: &$engine) -> $name {
                $name::zero(e)
            }
            fn group_mul_assign(&mut self, e: &$engine, scalar: &$scalarfield) {
                self.mul_assign(e, scalar);
            }
            fn group_add_assign(&mut self, e: &$engine, other: &Self) {
                self.add_assign(e, other);
            }
            fn group_sub_assign(&mut self, e: &$engine, other: &Self) {
                self.sub_assign(e, other);
            }
        }

        impl CurveAffine<$engine> for $name_affine {
            type Jacobian = $name;
            type Uncompressed = $name_uncompressed;

            fn is_valid(&self, e: &$engine) -> bool {
                if self.is_zero() {
                    true
                } else {
                    // Check that the point is on the curve
                    let mut y2 = self.y;
                    y2.square(e);

                    let mut x3b = self.x;
                    x3b.square(e);
                    x3b.mul_assign(e, &self.x);
                    x3b.add_assign(e, &e.$params_field.coeff_b);

                    if y2 == x3b {
                        // Check that the point is in the correct subgroup
                        if self.mul(e, &$scalarfield::char(e)).is_zero() {
                            true
                        } else {
                            false
                        }
                    } else {
                        false
                    }
                }
            }

            fn to_uncompressed(&self, engine: &$engine) -> Self::Uncompressed {
                $name_uncompressed::from_affine(self, engine)
            }

            fn to_jacobian(&self, engine: &$engine) -> $name {
                if self.infinity {
                    $name::zero(engine)
                } else {
                    $name {
                        x: self.x,
                        y: self.y,
                        z: $basefield::one(engine)
                    }
                }
            }

            fn prepare(self, e: &$engine) -> $name_prepared {
                $name_prepared::from_engine(e, self)
            }

            fn is_zero(&self) -> bool {
                self.infinity
            }

            fn mul<S: Convert<<$scalarfield as PrimeField<$engine>>::Repr, $engine>>(&self, e: &$engine, other: &S) -> $name {
                let mut res = $name::zero(e);

                for i in BitIterator::new((*other.convert(e)).borrow())
                {
                    res.double(e);

                    if i {
                        res.add_assign_mixed(e, self);
                    }
                }

                res
            }

            fn negate(&mut self, e: &$engine) {
                if !self.is_zero() {
                    self.y.negate(e);
                }
            }
        }

        impl multiexp::Projective<$engine> for $name {
            type WindowTable = wnaf::WindowTable<$engine, $name>;

            fn identity(e: &$engine) -> Self {
                Self::zero(e)
            }

            fn add_to_projective(&self, e: &$engine, projective: &mut Self) {
                projective.add_assign(e, self);
            }

            fn exponentiate(&mut self,
                            e: &$engine,
                            scalar: <$scalarfield as PrimeField<$engine>>::Repr,
                            table: &mut Self::WindowTable,
                            scratch: &mut wnaf::WNAFTable
            )
            {
                *self = self.optimal_exp(e, scalar, table, scratch);
            }

            fn new_window_table(e: &$engine) -> Self::WindowTable {
                wnaf::WindowTable::<$engine, $name>::new(e, $name::zero(e), 2)
            }
        }

        impl Curve<$engine> for $name {
            type Affine = $name_affine;
            type Prepared = $name_prepared;

            fn optimal_window(engine: &$engine, scalar_bits: usize) -> Option<usize> {
                for (i, bits) in engine.$params_field.windows.iter().enumerate().rev() {
                    if &scalar_bits >= bits {
                        return Some(i + 2);
                    }
                }

                None
            }

            fn optimal_window_batch(&self, engine: &$engine, scalars: usize) -> wnaf::WindowTable<$engine, $name> {
                let mut window = engine.$params_field.batch_windows.0;

                for i in &engine.$params_field.batch_windows.1 {
                    if scalars >= *i {
                        window += 1;
                    } else {
                        break;
                    }
                }

                wnaf::WindowTable::new(engine, *self, window)
            }

            fn zero(engine: &$engine) -> Self {
                engine.$params_field.zero
            }

            fn one(engine: &$engine) -> Self {
                engine.$params_field.one
            }

            fn random<R: rand::Rng>(engine: &$engine, rng: &mut R) -> Self {
                let mut tmp = Self::one(engine);
                tmp.mul_assign(engine, &$scalarfield::random(engine, rng));

                tmp
            }

            fn is_zero(&self) -> bool {
                self.z.is_zero()
            }

            fn is_equal(&self, engine: &$engine, other: &Self) -> bool {
                if self.is_zero() {
                    return other.is_zero();
                }

                if other.is_zero() {
                    return false;
                }

                let mut z1 = self.z;
                z1.square(engine);
                let mut z2 = other.z;
                z2.square(engine);

                let mut tmp1 = self.x;
                tmp1.mul_assign(engine, &z2);

                let mut tmp2 = other.x;
                tmp2.mul_assign(engine, &z1);

                if tmp1 != tmp2 {
                    return false;
                }

                z1.mul_assign(engine, &self.z);
                z2.mul_assign(engine, &other.z);
                z2.mul_assign(engine, &self.y);
                z1.mul_assign(engine, &other.y);

                if z1 != z2 {
                    return false;
                }

                true
            }

            fn to_affine(&self, engine: &$engine) -> Self::Affine {
                if self.is_zero() {
                    $name_affine {
                        x: $basefield::zero(),
                        y: $basefield::one(engine),
                        infinity: true
                    }
                } else {
                    let zinv = self.z.inverse(engine).unwrap();
                    let mut zinv_powered = zinv;
                    zinv_powered.square(engine);

                    let mut x = self.x;
                    x.mul_assign(engine, &zinv_powered);

                    let mut y = self.y;
                    zinv_powered.mul_assign(engine, &zinv);
                    y.mul_assign(engine, &zinv_powered);

                    $name_affine {
                        x: x,
                        y: y,
                        infinity: false
                    }
                }
            }

            fn prepare(&self, e: &$engine) -> $name_prepared {
                self.to_affine(e).prepare(e)
            }

            fn double(&mut self, engine: &$engine) {
                if self.is_zero() {
                    return;
                }

                let mut a = self.x;
                a.square(engine);
                let mut c = self.y;
                c.square(engine);
                let mut d = c;
                c.square(engine);
                d.add_assign(engine, &self.x);
                d.square(engine);
                d.sub_assign(engine, &a);
                d.sub_assign(engine, &c);
                d.double(engine);
                let mut e = a;
                e.add_assign(engine, &a);
                e.add_assign(engine, &a);
                self.x = e;
                self.x.square(engine);
                self.x.sub_assign(engine, &d);
                self.x.sub_assign(engine, &d);
                c.double(engine);
                c.double(engine);
                c.double(engine);
                self.z.mul_assign(engine, &self.y);
                self.z.double(engine);
                self.y = d;
                self.y.sub_assign(engine, &self.x);
                self.y.mul_assign(engine, &e);
                self.y.sub_assign(engine, &c);
            }

            fn negate(&mut self, engine: &$engine) {
                if !self.is_zero() {
                    self.y.negate(engine)
                }
            }

            fn mul_assign<S: Convert<<$scalarfield as PrimeField<$engine>>::Repr, $engine>>(&mut self, engine: &$engine, other: &S) {
                let mut res = Self::zero(engine);

                for i in BitIterator::new((*other.convert(engine)).borrow())
                {
                    res.double(engine);

                    if i {
                        res.add_assign(engine, self);
                    }
                }

                *self = res;
            }

            fn sub_assign(&mut self, engine: &$engine, other: &Self) {
                let mut tmp = *other;
                tmp.negate(engine);
                self.add_assign(engine, &tmp);
            }

            fn add_assign_mixed(&mut self, e: &$engine, other: &$name_affine) {
                if other.is_zero() {
                    return;
                }

                if self.is_zero() {
                    self.x = other.x;
                    self.y = other.y;
                    self.z = $basefield::one(e);
                    return;
                }
                
                let mut z1z1 = self.z;
                z1z1.square(e);
                let mut u2 = other.x;
                u2.mul_assign(e, &z1z1);
                let mut z1cubed = self.z;
                z1cubed.mul_assign(e, &z1z1);
                let mut s2 = other.y;
                s2.mul_assign(e, &z1cubed);

                if self.x == u2 && self.y == s2 {
                    self.double(e);
                    return;
                }

                let mut h = u2;
                h.sub_assign(e, &self.x);
                let mut hh = h;
                hh.square(e);
                let mut i = hh;
                i.double(e);
                i.double(e);
                let mut j = h;
                j.mul_assign(e, &i);
                let mut r = s2;
                r.sub_assign(e, &self.y);
                r.double(e);
                let mut v = self.x;
                v.mul_assign(e, &i);

                self.x = r;
                self.x.square(e);
                self.x.sub_assign(e, &j);
                self.x.sub_assign(e, &v);
                self.x.sub_assign(e, &v);

                self.y.mul_assign(e, &j);
                let mut tmp = v;
                tmp.sub_assign(e, &self.x);
                tmp.mul_assign(e, &r);
                tmp.sub_assign(e, &self.y);
                tmp.sub_assign(e, &self.y);
                self.y = tmp;

                self.z.add_assign(e, &h);
                self.z.square(e);
                self.z.sub_assign(e, &z1z1);
                self.z.sub_assign(e, &hh);
            }

            fn add_assign(&mut self, engine: &$engine, other: &Self) {
                if self.is_zero() {
                    *self = *other;
                    return;
                }

                if other.is_zero() {
                    return;
                }

                let mut z1_squared = self.z;
                z1_squared.square(engine);
                let mut z2_squared = other.z;
                z2_squared.square(engine);
                let mut u1 = self.x;
                u1.mul_assign(engine, &z2_squared);
                let mut u2 = other.x;
                u2.mul_assign(engine, &z1_squared);
                let mut s1 = other.z;
                s1.mul_assign(engine, &z2_squared);
                s1.mul_assign(engine, &self.y);
                let mut s2 = self.z;
                s2.mul_assign(engine, &z1_squared);
                s2.mul_assign(engine, &other.y);

                if u1 == u2 && s1 == s2 {
                    self.double(engine);
                } else {
                    u2.sub_assign(engine, &u1);
                    s2.sub_assign(engine, &s1);
                    s2.double(engine);
                    let mut i = u2;
                    i.double(engine);
                    i.square(engine);
                    let mut v = i;
                    v.mul_assign(engine, &u1);
                    i.mul_assign(engine, &u2);
                    s1.mul_assign(engine, &i);
                    s1.double(engine);
                    self.x = s2;
                    self.x.square(engine);
                    self.x.sub_assign(engine, &i);
                    self.x.sub_assign(engine, &v);
                    self.x.sub_assign(engine, &v);
                    self.y = v;
                    self.y.sub_assign(engine, &self.x);
                    self.y.mul_assign(engine, &s2);
                    self.y.sub_assign(engine, &s1);
                    self.z.add_assign(engine, &other.z);
                    self.z.square(engine);
                    self.z.sub_assign(engine, &z1_squared);
                    self.z.sub_assign(engine, &z2_squared);
                    self.z.mul_assign(engine, &u2);
                }
            }
        }
    }
}
