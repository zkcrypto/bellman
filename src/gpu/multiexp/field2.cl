// Fp2 Extension Field where u^2 + 1 = 0

#define FIELD2_LIMB_BITS FIELD_LIMB_BITS
#define FIELD2_ZERO ((FIELD2){FIELD_ZERO, FIELD_ZERO})
#define FIELD2_ONE ((FIELD2){FIELD_ONE, FIELD_ZERO})

typedef struct {
  FIELD c0;
  FIELD c1;
} FIELD2; // Represents: c0 + u * c1

bool FIELD2_eq(FIELD2 a, FIELD2 b) {
  return FIELD_eq(a.c0, b.c0) && FIELD_eq(a.c1, b.c1);
}
FIELD2 FIELD2_sub(FIELD2 a, FIELD2 b) {
  a.c0 = FIELD_sub(a.c0, b.c0);
  a.c1 = FIELD_sub(a.c1, b.c1);
  return a;
}
FIELD2 FIELD2_add(FIELD2 a, FIELD2 b) {
  a.c0 = FIELD_add(a.c0, b.c0);
  a.c1 = FIELD_add(a.c1, b.c1);
  return a;
}
FIELD2 FIELD2_double(FIELD2 a) {
  a.c0 = FIELD_double(a.c0);
  a.c1 = FIELD_double(a.c1);
  return a;
}

/*
 * (a_0 + u * a_1)(b_0 + u * b_1) = a_0 * b_0 - a_1 * b_1 + u * (a_0 * b_1 + a_1 * b_0)
 * Therefore:
 * c_0 = a_0 * b_0 - a_1 * b_1
 * c_1 = (a_0 * b_1 + a_1 * b_0) = (a_0 + a_1) * (b_0 + b_1) - a_0 * b_0 - a_1 * b_1
 */
FIELD2 FIELD2_mul(FIELD2 a, FIELD2 b) {
  const FIELD aa = FIELD_mul(a.c0, b.c0);
  const FIELD bb = FIELD_mul(a.c1, b.c1);
  const FIELD o = FIELD_add(b.c0, b.c1);
  a.c1 = FIELD_add(a.c1, a.c0);
  a.c1 = FIELD_mul(a.c1, o);
  a.c1 = FIELD_sub(a.c1, aa);
  a.c1 = FIELD_sub(a.c1, bb);
  a.c0 = FIELD_sub(aa, bb);
  return a;
}

/*
 * (a_0 + u * a_1)(a_0 + u * a_1) = a_0 ^ 2 - a_1 ^ 2 + u * 2 * a_0 * a_1
 * Therefore:
 * c_0 = (a_0 * a_0 - a_1 * a_1) = (a_0 + a_1)(a_0 - a_1)
 * c_1 = 2 * a_0 * a_1
 */
FIELD2 FIELD2_sqr(FIELD2 a) {
  const FIELD ab = FIELD_mul(a.c0, a.c1);
  const FIELD c0c1 = FIELD_add(a.c0, a.c1);
  a.c0 = FIELD_mul(FIELD_sub(a.c0, a.c1), c0c1);
  a.c1 = FIELD_double(ab);
  return a;
}
