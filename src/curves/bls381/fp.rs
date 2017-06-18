macro_rules! fp_params_impl {
    (
        $name:ident = (3 mod 4),
        engine = $engine:ident,
        params = $params_field:ident : $params_name:ident,
        limbs = $limbs:expr,
        modulus = $modulus:expr,
        r1 = $r1:expr,
        r2 = $r2:expr,
        modulus_minus_3_over_4 = $modulus_minus_3_over_4:expr,
        modulus_minus_1_over_2 = $modulus_minus_1_over_2:expr,
        inv = $inv:expr
    ) => {
        #[derive(Clone)]
        struct $params_name {
            modulus: [u64; $limbs],
            r1: $name,
            r2: $name,
            inv: u64,
            one: $name,
            num_bits: usize,
            modulus_minus_3_over_4: [u64; $limbs],
            modulus_minus_1_over_2: [u64; $limbs],
            base10: [$name; 11]
        }

        impl $params_name {
            fn partial_init() -> $params_name {
                let mut tmp = $params_name {
                    modulus: $modulus,
                    r1: $name($r1),
                    r2: $name($r2),
                    inv: $inv,
                    one: $name::zero(),
                    num_bits: 0,
                    modulus_minus_3_over_4: $modulus_minus_3_over_4,
                    modulus_minus_1_over_2: $modulus_minus_1_over_2,
                    base10: [$name::zero(); 11]
                };

                tmp.one.0[0] = 1;

                tmp
            }
        }
    };
    (
        $name:ident = (1 mod 16),
        engine = $engine:ident,
        params = $params_field:ident : $params_name:ident,
        limbs = $limbs:expr,
        modulus = $modulus:expr,
        r1 = $r1:expr,
        r2 = $r2:expr,
        modulus_minus_1_over_2 = $modulus_minus_1_over_2:expr,
        s = $s:expr,
        t = $t:expr,
        t_plus_1_over_2 = $t_plus_1_over_2:expr,
        inv = $inv:expr
    ) => {
        #[derive(Clone)]
        struct $params_name {
            modulus: [u64; $limbs],
            r1: $name,
            r2: $name,
            inv: u64,
            one: $name,
            num_bits: usize,
            modulus_minus_1_over_2: [u64; $limbs],
            s: u64,
            t: [u64; $limbs],
            t_plus_1_over_2: [u64; $limbs],
            root_of_unity: $name,
            multiplicative_generator: $name,
            base10: [$name; 11]
        }

        impl $params_name {
            fn partial_init() -> $params_name {
                let mut tmp = $params_name {
                    modulus: $modulus,
                    r1: $name($r1),
                    r2: $name($r2),
                    inv: $inv,
                    one: $name::zero(),
                    num_bits: 0,
                    modulus_minus_1_over_2: $modulus_minus_1_over_2,
                    s: $s,
                    t: $t,
                    t_plus_1_over_2: $t_plus_1_over_2,
                    root_of_unity: $name::zero(),
                    multiplicative_generator: $name::zero(),
                    base10: [$name::zero(); 11]
                };

                tmp.one.0[0] = 1;

                tmp
            }
        }
    };
}

macro_rules! fp_sqrt_impl {
    (
        $name:ident = (3 mod 4),
        engine = $engine:ident,
        params = $params_field:ident : $params_name:ident
    ) => {
        impl SqrtField<$engine> for $name {
            fn sqrt(&self, engine: &$engine) -> Option<Self> {
                let mut a1 = self.pow(engine, &engine.$params_field.modulus_minus_3_over_4);

                let mut a0 = a1;
                a0.square(engine);
                a0.mul_assign(engine, self);

                let mut neg1 = Self::one(engine);
                neg1.negate(engine);

                if a0 == neg1 {
                    None
                } else {
                    a1.mul_assign(engine, self);
                    Some(a1)
                }
            }
        }
    };
    (
        $name:ident = (1 mod 16),
        engine = $engine:ident,
        params = $params_field:ident : $params_name:ident
    ) => {
        impl SqrtField<$engine> for $name {
            fn sqrt(&self, engine: &$engine) -> Option<Self> {
                if self.is_zero() {
                    return Some(*self);
                }

                if self.pow(engine, &engine.$params_field.modulus_minus_1_over_2) != $name::one(engine) {
                    None
                } else {
                    let mut c = engine.$params_field.root_of_unity;

                    let mut r = self.pow(engine, &engine.$params_field.t_plus_1_over_2);
                    let mut t = self.pow(engine, &engine.$params_field.t);
                    let mut m = engine.$params_field.s;
                    
                    while t != Self::one(engine) {
                        let mut i = 1;
                        {
                            let mut t2i = t;
                            t2i.square(engine);
                            loop {
                                if t2i == Self::one(engine) {
                                    break;
                                }
                                t2i.square(engine);
                                i += 1;
                            }
                        }

                        for _ in 0..(m - i - 1) {
                            c.square(engine);
                        }
                        r.mul_assign(engine, &c);
                        c.square(engine);
                        t.mul_assign(engine, &c);
                        m = i;
                    }

                    Some(r)
                }
            }
        }
    };
}

macro_rules! fp_impl {
    (
        $name:ident = ($($congruency:tt)*),
        engine = $engine:ident,
        params = $params_field:ident : $params_name:ident,
        arith = $arith_mod:ident,
        repr = $repr:ident,
        limbs = $limbs:expr,
        $($params:tt)*
    ) => {
        fp_params_impl!(
            $name = ($($congruency)*),
            engine = $engine,
            params = $params_field : $params_name,
            limbs = $limbs,
            $($params)*
        );

        impl $params_name {
            fn base10(e: &$engine) -> [$name; 11] {
                let mut ret = [$name::zero(); 11];

                let mut acc = $name::zero();
                for i in 0..11 {
                    ret[i] = acc;
                    acc.add_assign(e, &$name::one(e));
                }

                ret
            }
        }

        fp_sqrt_impl!(
            $name = ($($congruency)*),
            engine = $engine,
            params = $params_field : $params_name
        );

        #[derive(Copy, Clone, PartialEq, Eq)]
        #[repr(C)]
        pub struct $name([u64; $limbs]);

        #[derive(Copy, Clone, PartialEq, Eq)]
        #[repr(C)]
        pub struct $repr([u64; $limbs]);

        impl PrimeFieldRepr for $repr {
            fn from_u64(a: u64) -> Self {
                let mut tmp: [u64; $limbs] = Default::default();
                tmp[0] = a;
                $repr(tmp)
            }

            fn sub_noborrow(&mut self, other: &Self) {
                $arith_mod::sub_noborrow(&mut self.0, &other.0);
            }

            fn add_nocarry(&mut self, other: &Self) {
                $arith_mod::add_nocarry(&mut self.0, &other.0);
            }

            fn num_bits(&self) -> usize {
                $arith_mod::num_bits(&self.0)
            }

            fn is_zero(&self) -> bool {
                self.0.iter().all(|&e| e==0)
            }

            fn is_odd(&self) -> bool {
                $arith_mod::odd(&self.0)
            }

            fn div2(&mut self) {
                $arith_mod::div2(&mut self.0);
            }
        }

        impl AsRef<[u64]> for $repr {
            fn as_ref(&self) -> &[u64] {
                &self.0
            }
        }

        impl Ord for $repr {
            fn cmp(&self, other: &$repr) -> Ordering {
                if $arith_mod::lt(&self.0, &other.0) {
                    Ordering::Less
                } else if self.0 == other.0 {
                    Ordering::Equal
                } else {
                    Ordering::Greater
                }
            }
        }

        impl PartialOrd for $repr {
            fn partial_cmp(&self, other: &$repr) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }

        impl fmt::Debug for $name
        {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                ENGINE.with(|e| {
                    try!(write!(f, "Fp(0x"));
                    for i in self.into_repr(&e).0.iter().rev() {
                        try!(write!(f, "{:016x}", *i));
                    }
                    write!(f, ")")
                })
            }
        }

        impl $name
        {
            #[inline]
            fn mont_reduce(&mut self, engine: &$engine, res: &mut [u64; $limbs*2]) {
                // The Montgomery reduction here is based on Algorithm 14.32 in
                // Handbook of Applied Cryptography
                // <http://cacr.uwaterloo.ca/hac/about/chap14.pdf>.

                for i in 0..$limbs {
                    let k = res[i].wrapping_mul(engine.$params_field.inv);
                    $arith_mod::mac_digit(&mut res[i..], &engine.$params_field.modulus, k);
                }

                self.0.copy_from_slice(&res[$limbs..]);

                self.reduce(engine);
            }

            #[inline]
            fn reduce(&mut self, engine: &$engine) {
                if !$arith_mod::lt(&self.0, &engine.$params_field.modulus) {
                    $arith_mod::sub_noborrow(&mut self.0, &engine.$params_field.modulus);
                }
            }
        }

        impl Convert<$repr, $engine> for $name
        {
            type Target = $repr;

            fn convert(&self, engine: &$engine) -> Cow<$repr> {
                Cow::Owned(self.into_repr(engine))
            }
        }

        impl PrimeField<$engine> for $name
        {
            type Repr = $repr;

            fn from_repr(engine: &$engine, repr: Self::Repr) -> Result<Self, ()> {
                let mut tmp = $name(repr.0);
                if $arith_mod::lt(&tmp.0, &engine.$params_field.modulus) {
                    tmp.mul_assign(engine, &engine.$params_field.r2);
                    Ok(tmp)
                } else {
                    Err(())
                }
            }

            fn into_repr(&self, engine: &$engine) -> Self::Repr {
                let mut tmp = *self;
                tmp.mul_assign(engine, &engine.$params_field.one);
                $repr(tmp.0)
            }

            fn from_u64(engine: &$engine, n: u64) -> Self {
                let mut r = [0; $limbs];
                r[0] = n;

                Self::from_repr(engine, $repr(r)).unwrap()
            }

            fn from_str(engine: &$engine, s: &str) -> Result<Self, ()> {
                let mut res = Self::zero();
                for c in s.chars() {
                    match c.to_digit(10) {
                        Some(d) => {
                            res.mul_assign(engine, &engine.$params_field.base10[10]);
                            res.add_assign(engine, &engine.$params_field.base10[d as usize]);
                        },
                        None => {
                            return Err(());
                        }
                    }
                }

                Ok(res)
            }

            fn char(engine: &$engine) -> Self::Repr {
                $repr(engine.$params_field.modulus)
            }

            fn num_bits(engine: &$engine) -> usize {
                engine.$params_field.num_bits
            }

            fn capacity(engine: &$engine) -> usize {
                Self::num_bits(engine) - 1
            }
        }

        impl Field<$engine> for $name
        {
            fn zero() -> Self {
                $name([0; $limbs])
            }

            fn one(engine: &$engine) -> Self {
                engine.$params_field.r1
            }

            fn random<R: rand::Rng>(engine: &$engine, rng: &mut R) -> Self {
                let mut tmp = [0; $limbs*2];
                for i in &mut tmp {
                    *i = rng.gen();
                }

                $name($arith_mod::divrem(&tmp, &engine.$params_field.modulus).1)
            }

            fn is_zero(&self) -> bool {
                self.0.iter().all(|&e| e==0)
            }

            fn double(&mut self, engine: &$engine) {
                $arith_mod::mul2(&mut self.0);

                self.reduce(engine);
            }

            fn frobenius_map(&mut self, _: &$engine, _: usize)
            {
                // This is the identity function for a prime field.
            }

            fn negate(&mut self, engine: &$engine) {
                if !self.is_zero() {
                    let mut tmp = engine.$params_field.modulus;
                    $arith_mod::sub_noborrow(&mut tmp, &self.0);
                    
                    self.0 = tmp;
                }
            }

            fn add_assign(&mut self, engine: &$engine, other: &Self) {
                $arith_mod::add_nocarry(&mut self.0, &other.0);

                self.reduce(engine);
            }

            fn sub_assign(&mut self, engine: &$engine, other: &Self) {
                if $arith_mod::lt(&self.0, &other.0) {
                    $arith_mod::add_nocarry(&mut self.0, &engine.$params_field.modulus);
                }

                $arith_mod::sub_noborrow(&mut self.0, &other.0);
            }

            fn square(&mut self, engine: &$engine)
            {
                let mut res = [0; $limbs*2];
                $arith_mod::mac3(&mut res, &self.0, &self.0);

                self.mont_reduce(engine, &mut res);
            }

            fn mul_assign(&mut self, engine: &$engine, other: &Self) {
                let mut res = [0; $limbs*2];
                $arith_mod::mac3(&mut res, &self.0, &other.0);

                self.mont_reduce(engine, &mut res);
            }

            fn inverse(&self, engine: &$engine) -> Option<Self> {
                if self.is_zero() {
                    None
                } else {
                    // Guajardo Kumar Paar Pelzl
                    // Efficient Software-Implementation of Finite Fields with Applications to Cryptography
                    // Algorithm 16 (BEA for Inversion in Fp)

                    let mut u = self.0;
                    let mut v = engine.$params_field.modulus;
                    let mut b = engine.$params_field.r2; // Avoids unnecessary reduction step.
                    let mut c = Self::zero();

                    while u != engine.$params_field.one.0 && v != engine.$params_field.one.0 {
                        while $arith_mod::even(&u) {
                            $arith_mod::div2(&mut u);

                            if $arith_mod::even(&b.0) {
                                $arith_mod::div2(&mut b.0);
                            } else {
                                $arith_mod::add_nocarry(&mut b.0, &engine.$params_field.modulus);
                                $arith_mod::div2(&mut b.0);
                            }
                        }

                        while $arith_mod::even(&v) {
                            $arith_mod::div2(&mut v);

                            if $arith_mod::even(&c.0) {
                                $arith_mod::div2(&mut c.0);
                            } else {
                                $arith_mod::add_nocarry(&mut c.0, &engine.$params_field.modulus);
                                $arith_mod::div2(&mut c.0);
                            }
                        }

                        if $arith_mod::lt(&v, &u) {
                            $arith_mod::sub_noborrow(&mut u, &v);
                            b.sub_assign(engine, &c);
                        } else {
                            $arith_mod::sub_noborrow(&mut v, &u);
                            c.sub_assign(engine, &b);
                        }
                    }

                    if u == engine.$params_field.one.0 {
                        Some(b)
                    } else {
                        Some(c)
                    }
                }
            }
        }

        mod $arith_mod {
            // Arithmetic
            #[allow(dead_code)]
            pub fn num_bits(v: &[u64; $limbs]) -> usize
            {
                let mut ret = 64 * $limbs;
                for i in v.iter().rev() {
                    let leading = i.leading_zeros() as usize;
                    ret -= leading;
                    if leading != 64 {
                        break;
                    }
                }

                ret
            }

            #[inline]
            pub fn mac_digit(acc: &mut [u64], b: &[u64], c: u64)
            {
                #[inline]
                fn mac_with_carry(a: u64, b: u64, c: u64, carry: &mut u64) -> u64 {
                    let tmp = (a as u128) + (b as u128) * (c as u128) + (*carry as u128);

                    *carry = (tmp >> 64) as u64;

                    tmp as u64
                }

                let mut b_iter = b.iter();
                let mut carry = 0;

                for ai in acc.iter_mut() {
                    if let Some(bi) = b_iter.next() {
                        *ai = mac_with_carry(*ai, *bi, c, &mut carry);
                    } else {
                        *ai = mac_with_carry(*ai, 0, c, &mut carry);
                    }
                }

                debug_assert!(carry == 0);
            }

            #[inline]
            pub fn mac3_long(acc: &mut [u64], b: &[u64], c: &[u64]) {
                for (i, xi) in b.iter().enumerate() {
                    mac_digit(&mut acc[i..], c, *xi);
                }
            }

            #[inline]
            pub fn mac3(acc: &mut [u64; $limbs*2], b: &[u64; $limbs], c: &[u64; $limbs]) {
                if $limbs > 4 {
                    let (x0, x1) = b.split_at($limbs / 2);
                    let (y0, y1) = c.split_at($limbs / 2);

                    let mut p = [0; $limbs+1];
                    mac3_long(&mut p, x1, y1);
                    add_nocarry(&mut acc[$limbs/2..], &p);
                    add_nocarry(&mut acc[$limbs..], &p);
                    p = [0; $limbs+1];
                    mac3_long(&mut p, x0, y0);
                    add_nocarry(&mut acc[..], &p);
                    add_nocarry(&mut acc[$limbs/2..], &p);

                    let mut sign;
                    let mut j0 = [0; $limbs / 2];
                    let mut j1 = [0; $limbs / 2];
                    if lt(x1, x0) {
                        sign = false;
                        j0.copy_from_slice(x0);
                        sub_noborrow(&mut j0, x1);
                    } else {
                        sign = true;
                        j0.copy_from_slice(x1);
                        sub_noborrow(&mut j0, x0);
                    }
                    if lt(&y1, &y0) {
                        sign = sign == false;
                        j1.copy_from_slice(y0);
                        sub_noborrow(&mut j1, y1);
                    } else {
                        sign = sign == true;
                        j1.copy_from_slice(y1);
                        sub_noborrow(&mut j1, y0);
                    }

                    if sign {
                        p = [0; $limbs+1];
                        mac3_long(&mut p, &j0, &j1);
                        sub_noborrow(&mut acc[$limbs/2..], &p);
                    } else {
                        mac3_long(&mut acc[$limbs/2..], &j0, &j1);
                    }
                } else {
                    mac3_long(acc, b, c);
                }
            }

            #[inline]
            pub fn adc(a: u64, b: u64, carry: &mut u64) -> u64 {
                let tmp = (a as u128) + (b as u128) + (*carry as u128);

                *carry = (tmp >> 64) as u64;

                tmp as u64
            }

            #[inline]
            #[allow(dead_code)]
            pub fn add_carry(a: &mut [u64], b: &[u64]) {
                use std::iter;

                let mut carry = 0;

                for (a, b) in a.into_iter().zip(b.iter().chain(iter::repeat(&0))) {
                    *a = adc(*a, *b, &mut carry);
                }

                debug_assert!(0 == carry);
            }

            #[inline]
            pub fn add_nocarry(a: &mut [u64], b: &[u64]) {
                let mut carry = 0;

                for (a, b) in a.into_iter().zip(b.iter()) {
                    *a = adc(*a, *b, &mut carry);
                }

                debug_assert!(0 == carry);
            }

            /// Returns true if a < b.
            #[inline]
            pub fn lt(a: &[u64], b: &[u64]) -> bool {
                for (a, b) in a.iter().zip(b.iter()).rev() {
                    if *a > *b {
                        return false;
                    } else if *a < *b {
                        return true;
                    }
                }

                false
            }

            #[inline]
            pub fn sub_noborrow(a: &mut [u64], b: &[u64]) {
                #[inline]
                fn sbb(a: u64, b: u64, borrow: &mut u64) -> u64 {
                    let tmp = (1u128 << 64) + (a as u128) - (b as u128) - (*borrow as u128);

                    *borrow = if tmp >> 64 == 0 { 1 } else { 0 };

                    tmp as u64
                }

                let mut borrow = 0;

                for (a, b) in a.into_iter().zip(b.iter()) {
                    *a = sbb(*a, *b, &mut borrow);
                }

                debug_assert!(0 == borrow);
            }

            /// Returns if number is even.
            #[inline(always)]
            #[allow(dead_code)]
            pub fn even(a: &[u64; $limbs]) -> bool {
                a[0] & 1 == 0
            }

            #[inline(always)]
            #[allow(dead_code)]
            pub fn odd(a: &[u64; $limbs]) -> bool {
                a[0] & 1 == 1
            }

            /// Divide by two
            #[inline]
            pub fn div2(a: &mut [u64; $limbs]) {
                let mut t = 0;
                for i in a.iter_mut().rev() {
                    let t2 = *i << 63;
                    *i >>= 1;
                    *i |= t;
                    t = t2;
                }
            }

            #[inline]
            pub fn mul2(a: &mut [u64; $limbs]) {
                let mut last = 0;
                for i in a {
                    let tmp = *i >> 63;
                    *i <<= 1;
                    *i |= last;
                    last = tmp;
                }
            }

            fn get_bit(this: &[u64; $limbs*2], n: usize) -> bool {
                let part = n / 64;
                let bit = n - (64 * part);

                this[part] & (1 << bit) > 0
            }

            fn set_bit(this: &mut [u64; $limbs], n: usize, to: bool) -> bool
            {
                let part = n / 64;
                let bit = n - (64 * part);

                match this.get_mut(part) {
                    Some(e) => {
                        if to {
                            *e |= 1 << bit;
                        } else {
                            *e &= !(1 << bit);
                        }

                        true
                    },
                    None => false
                }
            }

            pub fn divrem(
                this: &[u64; $limbs*2],
                modulo: &[u64; $limbs]
            ) -> (Option<[u64; $limbs]>, [u64; $limbs])
            {
                let mut q = Some([0; $limbs]);
                let mut r = [0; $limbs];

                for i in (0..($limbs*2*64)).rev() {
                    // NB: modulo's first bit is unset so this will never
                    // destroy information
                    mul2(&mut r);
                    assert!(set_bit(&mut r, 0, get_bit(this, i)));
                    if !lt(&r, modulo) {
                        sub_noborrow(&mut r, modulo);
                        if q.is_some() && !set_bit(q.as_mut().unwrap(), i, true) {
                            q = None
                        }
                    }
                }

                if q.is_some() && !lt(q.as_ref().unwrap(), modulo) {
                    (None, r)
                } else {
                    (q, r)
                }
            }
        }
    }
}
