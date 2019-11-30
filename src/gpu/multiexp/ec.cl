// Elliptic curve operations (Short Weierstrass Jacobian form)

#define POINT_ZERO ((POINT_projective){FIELD_ZERO, FIELD_ONE, FIELD_ZERO})

typedef struct {
  FIELD x;
  FIELD y;
  bool inf;
} POINT_affine;

typedef struct {
  FIELD x;
  FIELD y;
  FIELD z;
} POINT_projective;

// http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#doubling-dbl-2009-l
POINT_projective POINT_double(POINT_projective inp) {
  if(FIELD_eq(inp.z, FIELD_ZERO)) return inp;
  FIELD a = FIELD_sqr(inp.x); // A = X1^2
  FIELD b = FIELD_sqr(inp.y); // B = Y1^2
  FIELD c = FIELD_sqr(b); // C = B^2

  // D = 2*((X1+B)2-A-C)
  FIELD d = FIELD_add(inp.x, b);
  d = FIELD_sqr(d); d = FIELD_sub(FIELD_sub(d, a), c); d = FIELD_double(d);

  FIELD e = FIELD_add(FIELD_double(a), a); // E = 3*A

  FIELD f = FIELD_sqr(e);

  inp.z = FIELD_mul(inp.y, inp.z); inp.z = FIELD_double(inp.z); // Z3 = 2*Y1*Z1
  inp.x = FIELD_sub(FIELD_sub(f, d), d); // X3 = F-2*D

  // Y3 = E*(D-X3)-8*C
  c = FIELD_double(c); c = FIELD_double(c); c = FIELD_double(c);
  inp.y = FIELD_sub(FIELD_mul(FIELD_sub(d, inp.x), e), c);

  return inp;
}

// http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-madd-2007-bl
POINT_projective POINT_add_mixed(POINT_projective a, POINT_affine b) {
  if(b.inf) return a;

  if(FIELD_eq(a.z, FIELD_ZERO)) {
    a.x = b.x;
    a.y = b.y;
    a.z = FIELD_ONE;
    return a;
  }

  FIELD z1z1 = FIELD_sqr(a.z);
  FIELD u2 = FIELD_mul(b.x, z1z1);
  FIELD s2 = FIELD_mul(FIELD_mul(b.y, a.z), z1z1);

  if(FIELD_eq(a.x, u2) && FIELD_eq(a.y, s2))
    return POINT_double(a);
  else {
    FIELD h = FIELD_sub(u2, a.x); // H = U2-X1
    FIELD hh = FIELD_sqr(h); // HH = H^2
    FIELD i = FIELD_double(hh); i = FIELD_double(i); // I = 4*HH
    FIELD j = FIELD_mul(h, i); // J = H*I
    FIELD r = FIELD_sub(s2, a.y); r = FIELD_double(r); // r = 2*(S2-Y1)
    FIELD v = FIELD_mul(a.x, i);

    POINT_projective ret;

     // X3 = r^2 - J - 2*V
    ret.x = FIELD_sub(FIELD_sub(FIELD_sqr(r), j), FIELD_double(v));

     // Y3 = r*(V-X3)-2*Y1*J
    j = FIELD_mul(a.y, j); j = FIELD_double(j);
    ret.y = FIELD_sub(FIELD_mul(FIELD_sub(v, ret.x), r), j);

    // Z3 = (Z1+H)^2-Z1Z1-HH
    ret.z = FIELD_add(a.z, h); ret.z = FIELD_sub(FIELD_sub(FIELD_sqr(ret.z), z1z1), hh);
    return ret;
  }
}

// http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-add-2007-bl
POINT_projective POINT_add(POINT_projective a, POINT_projective b) {

  if(FIELD_eq(a.z, FIELD_ZERO)) return b;
  if(FIELD_eq(b.z, FIELD_ZERO)) return a;

  FIELD z1z1 = FIELD_sqr(a.z); // Z1Z1 = Z1^2
  FIELD z2z2 = FIELD_sqr(b.z); // Z2Z2 = Z2^2
  FIELD u1 = FIELD_mul(a.x, z2z2); // U1 = X1*Z2Z2
  FIELD u2 = FIELD_mul(b.x, z1z1); // U2 = X2*Z1Z1
  FIELD s1 = FIELD_mul(FIELD_mul(a.y, b.z), z2z2); // S1 = Y1*Z2*Z2Z2
  FIELD s2 = FIELD_mul(FIELD_mul(b.y, a.z), z1z1); // S2 = Y2*Z1*Z1Z1

  if(FIELD_eq(u1, u2) && FIELD_eq(s1, s2))
    return POINT_double(a);
  else {
    FIELD h = FIELD_sub(u2, u1); // H = U2-U1
    FIELD i = FIELD_double(h); i = FIELD_sqr(i); // I = (2*H)^2
    FIELD j = FIELD_mul(h, i); // J = H*I
    FIELD r = FIELD_sub(s2, s1); r = FIELD_double(r); // r = 2*(S2-S1)
    FIELD v = FIELD_mul(u1, i); // V = U1*I
    a.x = FIELD_sub(FIELD_sub(FIELD_sub(FIELD_sqr(r), j), v), v); // X3 = r^2 - J - 2*V

    // Y3 = r*(V - X3) - 2*S1*J
    a.y = FIELD_mul(FIELD_sub(v, a.x), r);
    s1 = FIELD_mul(s1, j); s1 = FIELD_double(s1); // S1 = S1 * J * 2
    a.y = FIELD_sub(a.y, s1);

    // Z3 = ((Z1+Z2)^2 - Z1Z1 - Z2Z2)*H
    a.z = FIELD_add(a.z, b.z); a.z = FIELD_sqr(a.z);
    a.z = FIELD_sub(FIELD_sub(a.z, z1z1), z2z2);
    a.z = FIELD_mul(a.z, h);

    return a;
  }
}
