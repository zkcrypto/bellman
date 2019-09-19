// FinalityLabs - 2019
// Arbitrary size prime-field arithmetic library (add, sub, mul, pow)

typedef struct { limb val[FIELD_LIMBS]; } FIELD;

// Greater than or equal
bool FIELD_gte(FIELD a, FIELD b) {
  for(char i = FIELD_LIMBS - 1; i >= 0; i--){
    if(a.val[i] > b.val[i])
      return true;
    if(a.val[i] < b.val[i])
      return false;
  }
  return true;
}

// Equals
bool FIELD_eq(FIELD a, FIELD b) {
  for(uchar i = 0; i < FIELD_LIMBS; i++)
    if(a.val[i] != b.val[i])
      return false;
  return true;
}

// Normal addition
FIELD FIELD_add_(FIELD a, FIELD b) {
  bool carry = 0;
  for(uchar i = 0; i < FIELD_LIMBS; i++) {
    limb old = a.val[i];
    a.val[i] += b.val[i] + carry;
    carry = carry ? old >= a.val[i] : old > a.val[i];
  }
  return a;
}

// Normal subtraction
FIELD FIELD_sub_(FIELD a, FIELD b) {
  bool borrow = 0;
  for(uchar i = 0; i < FIELD_LIMBS; i++) {
    limb old = a.val[i];
    a.val[i] -= b.val[i] + borrow;
    borrow = borrow ? old <= a.val[i] : old < a.val[i];
  }
  return a;
}

/*
 * Montgomery reduction
 * Takes the result of a long multiplication (Which has twice the size of a FIELD)
 * as input and reduces it to a FIELD.
 * Learn more:
 * https://en.wikipedia.org/wiki/Montgomery_modular_multiplication
 * https://alicebob.cryptoland.net/understanding-the-montgomery-reduction-algorithm/
 */
FIELD FIELD_reduce(limb *limbs) {
  bool carry2 = 0;
  for(uchar i = 0; i < FIELD_LIMBS; i++) {
    limb u = FIELD_INV * limbs[i];
    limb carry = 0;
    for(uchar j = 0; j < FIELD_LIMBS; j++)
      limbs[i + j] = mac_with_carry(u, FIELD_P.val[j], limbs[i + j], &carry);
    limbs[i + FIELD_LIMBS] = add2_with_carry(limbs[i + FIELD_LIMBS], carry, &carry2);
  }

  // Divide by R (Or take the upper half of `limbs` array as the final result)
  FIELD result;
  for(uchar i = 0; i < FIELD_LIMBS; i++) result.val[i] = limbs[i+FIELD_LIMBS];

  if(FIELD_gte(result, FIELD_P))
    result = FIELD_sub_(result, FIELD_P);

  return result;
}

// Modular multiplication
FIELD FIELD_mul(FIELD a, FIELD b) {

  // Long multiplication
  // https://en.wikipedia.org/wiki/Multiplication_algorithm#Long_multiplication
  limb res[FIELD_LIMBS * 2] = {0};
  for(uchar i = 0; i < FIELD_LIMBS; i++) {
    limb carry = 0;
    for(uchar j = 0; j < FIELD_LIMBS; j++)
      res[i + j] = mac_with_carry(a.val[i], b.val[j], res[i + j], &carry);
    res[i + FIELD_LIMBS] = carry;
  }

  // Result doesn't fit into a FIELD, so a Montgomery reduction is needed.
  return FIELD_reduce(res);
}

// Modular subtraction
FIELD FIELD_sub(FIELD a, FIELD b) {
  FIELD res = FIELD_sub_(a, b);
  if(!FIELD_gte(a, b)) res = FIELD_add_(res, FIELD_P);
  return res;
}

// Modular addition
FIELD FIELD_add(FIELD a, FIELD b) {
  FIELD res = FIELD_add_(a, b);
  if(FIELD_gte(res, FIELD_P)) res = FIELD_sub_(res, FIELD_P);
  return res;
}

// Squaring is a special case of multiplication which can be done ~1.5x faster.
// https://stackoverflow.com/a/16388571/1348497
FIELD FIELD_sqr(FIELD a) {

  // Long multiplication (Diagonal elements are skipped)
  limb res[FIELD_LIMBS * 2] = {0};
  for(uchar i = 0; i < FIELD_LIMBS - 1; i++) {
    limb carry = 0;
    for(uchar j = i + 1; j < FIELD_LIMBS; j++)
      res[i + j] = mac_with_carry(a.val[i], a.val[j], res[i + j], &carry);
    res[i + FIELD_LIMBS] = carry;
  }

  // Double the result
  res[FIELD_LIMBS * 2 - 1] = res[FIELD_LIMBS * 2 - 2] >> (LIMB_BITS - 1);
  for(uchar i = FIELD_LIMBS * 2 - 2; i > 1; i--)
    res[i] = (res[i] << 1) | (res[i - 1] >> (LIMB_BITS - 1));
  res[1] <<= 1;

  // Process diagonal elements
  limb carry = 0;
  for(uchar i = 0; i < FIELD_LIMBS; i++) {
    res[i * 2] = mac_with_carry(a.val[i], a.val[i], res[i * 2], &carry);
    res[i * 2 + 1] = add_with_carry(res[i * 2 + 1], &carry);
  }

  return FIELD_reduce(res);
}

// Left-shift the limbs by one bit and subtract by modulus in case of overflow.
// Faster version of FIELD_add(a, a)
FIELD FIELD_double(FIELD a) {
  for(uchar i = FIELD_LIMBS - 1; i >= 1; i--)
    a.val[i] = (a.val[i] << 1) | (a.val[i - 1] >> (LIMB_BITS - 1));
  a.val[0] <<= 1;
  if(FIELD_gte(a, FIELD_P)) a = FIELD_sub_(a, FIELD_P);
  return a;
}

// Modular exponentiation (Exponentiation by Squaring)
// https://en.wikipedia.org/wiki/Exponentiation_by_squaring
FIELD FIELD_pow(FIELD base, uint exponent) {
  FIELD res = FIELD_ONE;
  while(exponent > 0) {
    if (exponent & 1)
      res = FIELD_mul(res, base);
    exponent = exponent >> 1;
    base = FIELD_sqr(base);
  }
  return res;
}


// Store squares of the base in a lookup table for faster evaluation.
FIELD FIELD_pow_lookup(__global FIELD *bases, uint exponent) {
  FIELD res = FIELD_ONE;
  uint i = 0;
  while(exponent > 0) {
    if (exponent & 1)
      res = FIELD_mul(res, bases[i]);
    exponent = exponent >> 1;
    i++;
  }
  return res;
}
