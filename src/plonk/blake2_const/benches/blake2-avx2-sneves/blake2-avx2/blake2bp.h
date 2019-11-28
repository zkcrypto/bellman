#ifndef BLAKE2_AVX2_BLAKE2BP_H
#define BLAKE2_AVX2_BLAKE2BP_H

#include <stddef.h>

int blake2bp(unsigned char * out, const unsigned char * in, size_t inlen);

#if defined(SUPERCOP)
int crypto_hash(unsigned char *out, const unsigned char *in, unsigned long long inlen);
#endif

#endif
