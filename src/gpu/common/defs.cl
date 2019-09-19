#ifdef __NV_CL_C_VERSION
#define NVIDIA
#endif

typedef ulong limb;
#define LIMB_BITS (64)

// Returns a * b + c + d, puts the carry in d
limb mac_with_carry(limb a, limb b, limb c, limb *d) {
  #ifdef NVIDIA
    limb lo, hi;
    asm("mad.lo.cc.u64 %0, %2, %3, %4;\r\n"
        "madc.hi.u64 %1, %2, %3, 0;\r\n"
        "add.cc.u64 %0, %0, %5;\r\n"
        "addc.u64 %1, %1, 0;\r\n"
        : "=l"(lo), "=l"(hi) : "l"(a), "l"(b), "l"(c), "l"(*d));
    *d = hi;
    return lo;
  #else
    limb lo = a * b + c;
    limb hi = mad_hi(a, b, (limb)(lo < c));
    a = lo;
    lo += *d;
    hi += (lo < a);
    *d = hi;
    return lo;
  #endif
}

// Returns a + b, puts the carry in d
limb add_with_carry(limb a, limb *b) {
  #ifdef NVIDIA
    limb lo, hi;
    asm("add.cc.u64 %0, %2, %3;\r\n"
        "addc.u64 %1, 0, 0;\r\n"
        : "=l"(lo), "=l"(hi) : "l"(a), "l"(*b));
    *b = hi;
    return lo;
  #else
    limb lo = a + *b;
    *b = lo < a;
    return lo;
  #endif
}

// Returns a + b + c, puts the carry in c
limb add2_with_carry(limb a, limb b, bool *c) {
  #ifdef NVIDIA
    limb lo, hi, cc = *c;
    asm("add.cc.u64 %0, %2, %3;\r\n"
        "addc.u64 %1, 0, 0;\r\n"
        "add.cc.u64 %0, %0, %4;\r\n"
        "addc.u64 %1, %1, 0;\r\n"
        : "=l"(lo), "=l"(hi) : "l"(a), "l"(b), "l"(cc));
    *c = hi;
    return lo;
  #else
    limb lo = a + b;
    limb hi = lo < a;
    a = lo;
    lo += *c;
    hi += (lo < a);
    *c = hi;
    return lo;
  #endif
}
