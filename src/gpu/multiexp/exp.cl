#define EXPONENT_BITS (EXPONENT_LIMBS * LIMB_BITS)

typedef struct { limb val[EXPONENT_LIMBS]; } EXPONENT;

// Get `i`th bit (From most significant digit) of the exponent.
bool EXPONENT_get_bit(EXPONENT l, uint i) {
  return (l.val[EXPONENT_LIMBS - 1 - i / LIMB_BITS] >> (LIMB_BITS - 1 - (i % LIMB_BITS))) & 1;
}

// Get `window` consecutive bits, (Starting from `skip`th bit) from the exponent.
uint EXPONENT_get_bits(EXPONENT l, uint skip, uint window) {
  uint ret = 0;
  for(uint i = 0; i < window; i++) {
    ret <<= 1;
    ret |= EXPONENT_get_bit(l, skip + i);
  }
  return ret;
}
