#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "blake2.h"
#include "blake2b.h"
#include "blake2b-common.h"

ALIGN(64) static const uint64_t blake2b_IV[8] = {
  UINT64_C(0x6A09E667F3BCC908), UINT64_C(0xBB67AE8584CAA73B),
  UINT64_C(0x3C6EF372FE94F82B), UINT64_C(0xA54FF53A5F1D36F1),
  UINT64_C(0x510E527FADE682D1), UINT64_C(0x9B05688C2B3E6C1F),
  UINT64_C(0x1F83D9ABFB41BD6B), UINT64_C(0x5BE0CD19137E2179),
};

#define BLAKE2B_G1_V1(a, b, c, d, m) do {     \
  a = ADD(a, m);                              \
  a = ADD(a, b); d = XOR(d, a); d = ROT32(d); \
  c = ADD(c, d); b = XOR(b, c); b = ROT24(b); \
} while(0)

#define BLAKE2B_G2_V1(a, b, c, d, m) do {     \
  a = ADD(a, m);                              \
  a = ADD(a, b); d = XOR(d, a); d = ROT16(d); \
  c = ADD(c, d); b = XOR(b, c); b = ROT63(b); \
} while(0)

#define BLAKE2B_DIAG_V1(a, b, c, d) do {                 \
  a = _mm256_permute4x64_epi64(a, _MM_SHUFFLE(2,1,0,3)); \
  d = _mm256_permute4x64_epi64(d, _MM_SHUFFLE(1,0,3,2)); \
  c = _mm256_permute4x64_epi64(c, _MM_SHUFFLE(0,3,2,1)); \
} while(0)

#define BLAKE2B_UNDIAG_V1(a, b, c, d) do {               \
  a = _mm256_permute4x64_epi64(a, _MM_SHUFFLE(0,3,2,1)); \
  d = _mm256_permute4x64_epi64(d, _MM_SHUFFLE(1,0,3,2)); \
  c = _mm256_permute4x64_epi64(c, _MM_SHUFFLE(2,1,0,3)); \
} while(0)

#if defined(PERMUTE_WITH_SHUFFLES)
  #include "blake2b-load-avx2.h"
#elif defined(PERMUTE_WITH_GATHER)
#else
  #include "blake2b-load-avx2-simple.h"
#endif

#if defined(PERMUTE_WITH_GATHER)
ALIGN(64) static const uint32_t indices[12][16] = {
  { 0,  2,  4,  6,  1,  3,  5,  7, 14,  8, 10, 12, 15,  9, 11, 13},
  {14,  4,  9, 13, 10,  8, 15,  6,  5,  1,  0, 11,  3, 12,  2,  7},
  {11, 12,  5, 15,  8,  0,  2, 13,  9, 10,  3,  7,  4, 14,  6,  1},
  { 7,  3, 13, 11,  9,  1, 12, 14, 15,  2,  5,  4,  8,  6, 10,  0},
  { 9,  5,  2, 10,  0,  7,  4, 15,  3, 14, 11,  6, 13,  1, 12,  8},
  { 2,  6,  0,  8, 12, 10, 11,  3,  1,  4,  7, 15,  9, 13,  5, 14},
  {12,  1, 14,  4,  5, 15, 13, 10,  8,  0,  6,  9, 11,  7,  3,  2},
  {13,  7, 12,  3, 11, 14,  1,  9,  2,  5, 15,  8, 10,  0,  4,  6},
  { 6, 14, 11,  0, 15,  9,  3,  8, 10, 12, 13,  1,  5,  2,  7,  4},
  {10,  8,  7,  1,  2,  4,  6,  5, 13, 15,  9,  3,  0, 11, 14, 12},
  { 0,  2,  4,  6,  1,  3,  5,  7, 14,  8, 10, 12, 15,  9, 11, 13},
  {14,  4,  9, 13, 10,  8, 15,  6,  5,  1,  0, 11,  3, 12,  2,  7},
};

#define BLAKE2B_ROUND_V1(a, b, c, d, r, m) do {                              \
  __m256i b0;                                                                \
  b0 = _mm256_i32gather_epi64((void *)(m), LOAD128(&indices[r][ 0]), 8);     \
  BLAKE2B_G1_V1(a, b, c, d, b0);                                             \
  b0 = _mm256_i32gather_epi64((void *)(m), LOAD128(&indices[r][ 4]), 8);     \
  BLAKE2B_G2_V1(a, b, c, d, b0);                                             \
  BLAKE2B_DIAG_V1(a, b, c, d);                                               \
  b0 = _mm256_i32gather_epi64((void *)(m), LOAD128(&indices[r][ 8]), 8);     \
  BLAKE2B_G1_V1(a, b, c, d, b0);                                             \
  b0 = _mm256_i32gather_epi64((void *)(m), LOAD128(&indices[r][12]), 8);     \
  BLAKE2B_G2_V1(a, b, c, d, b0);                                             \
  BLAKE2B_UNDIAG_V1(a, b, c, d);                                             \
} while(0)

#define BLAKE2B_ROUNDS_V1(a, b, c, d, m) do { \
  int i;                                      \
  for(i = 0; i < 12; ++i) {                   \
    BLAKE2B_ROUND_V1(a, b, c, d, i, m);       \
  }                                           \
} while(0)
#else /* !PERMUTE_WITH_GATHER */
#define BLAKE2B_ROUND_V1(a, b, c, d, r, m) do { \
  __m256i b0;                                   \
  BLAKE2B_LOAD_MSG_ ##r ##_1(b0);               \
  BLAKE2B_G1_V1(a, b, c, d, b0);                \
  BLAKE2B_LOAD_MSG_ ##r ##_2(b0);               \
  BLAKE2B_G2_V1(a, b, c, d, b0);                \
  BLAKE2B_DIAG_V1(a, b, c, d);                  \
  BLAKE2B_LOAD_MSG_ ##r ##_3(b0);               \
  BLAKE2B_G1_V1(a, b, c, d, b0);                \
  BLAKE2B_LOAD_MSG_ ##r ##_4(b0);               \
  BLAKE2B_G2_V1(a, b, c, d, b0);                \
  BLAKE2B_UNDIAG_V1(a, b, c, d);                \
} while(0)

#define BLAKE2B_ROUNDS_V1(a, b, c, d, m) do {   \
  BLAKE2B_ROUND_V1(a, b, c, d,  0, (m));        \
  BLAKE2B_ROUND_V1(a, b, c, d,  1, (m));        \
  BLAKE2B_ROUND_V1(a, b, c, d,  2, (m));        \
  BLAKE2B_ROUND_V1(a, b, c, d,  3, (m));        \
  BLAKE2B_ROUND_V1(a, b, c, d,  4, (m));        \
  BLAKE2B_ROUND_V1(a, b, c, d,  5, (m));        \
  BLAKE2B_ROUND_V1(a, b, c, d,  6, (m));        \
  BLAKE2B_ROUND_V1(a, b, c, d,  7, (m));        \
  BLAKE2B_ROUND_V1(a, b, c, d,  8, (m));        \
  BLAKE2B_ROUND_V1(a, b, c, d,  9, (m));        \
  BLAKE2B_ROUND_V1(a, b, c, d, 10, (m));        \
  BLAKE2B_ROUND_V1(a, b, c, d, 11, (m));        \
} while(0)
#endif

#if defined(PERMUTE_WITH_GATHER)
#define DECLARE_MESSAGE_WORDS(m)
#elif defined(PERMUTE_WITH_SHUFFLES)
#define DECLARE_MESSAGE_WORDS(m)                                       \
  const __m256i m0 = _mm256_broadcastsi128_si256(LOADU128((m) +   0)); \
  const __m256i m1 = _mm256_broadcastsi128_si256(LOADU128((m) +  16)); \
  const __m256i m2 = _mm256_broadcastsi128_si256(LOADU128((m) +  32)); \
  const __m256i m3 = _mm256_broadcastsi128_si256(LOADU128((m) +  48)); \
  const __m256i m4 = _mm256_broadcastsi128_si256(LOADU128((m) +  64)); \
  const __m256i m5 = _mm256_broadcastsi128_si256(LOADU128((m) +  80)); \
  const __m256i m6 = _mm256_broadcastsi128_si256(LOADU128((m) +  96)); \
  const __m256i m7 = _mm256_broadcastsi128_si256(LOADU128((m) + 112)); \
  __m256i t0, t1;
#else
#define DECLARE_MESSAGE_WORDS(m)           \
  const uint64_t  m0 = LOADU64((m) +   0); \
  const uint64_t  m1 = LOADU64((m) +   8); \
  const uint64_t  m2 = LOADU64((m) +  16); \
  const uint64_t  m3 = LOADU64((m) +  24); \
  const uint64_t  m4 = LOADU64((m) +  32); \
  const uint64_t  m5 = LOADU64((m) +  40); \
  const uint64_t  m6 = LOADU64((m) +  48); \
  const uint64_t  m7 = LOADU64((m) +  56); \
  const uint64_t  m8 = LOADU64((m) +  64); \
  const uint64_t  m9 = LOADU64((m) +  72); \
  const uint64_t m10 = LOADU64((m) +  80); \
  const uint64_t m11 = LOADU64((m) +  88); \
  const uint64_t m12 = LOADU64((m) +  96); \
  const uint64_t m13 = LOADU64((m) + 104); \
  const uint64_t m14 = LOADU64((m) + 112); \
  const uint64_t m15 = LOADU64((m) + 120);
#endif

#define BLAKE2B_COMPRESS_V1(a, b, m, t0, t1, f0, f1) do { \
  DECLARE_MESSAGE_WORDS(m)                                \
  const __m256i iv0 = a;                                  \
  const __m256i iv1 = b;                                  \
  __m256i c = LOAD(&blake2b_IV[0]);                       \
  __m256i d = XOR(                                        \
    LOAD(&blake2b_IV[4]),                                 \
    _mm256_set_epi64x(f1, f0, t1, t0)                     \
  );                                                      \
  BLAKE2B_ROUNDS_V1(a, b, c, d, m);                       \
  a = XOR(a, c);                                          \
  b = XOR(b, d);                                          \
  a = XOR(a, iv0);                                        \
  b = XOR(b, iv1);                                        \
} while(0)

int blake2b(uint8_t * out, const uint8_t * in, size_t inlen) {
  const __m256i parameter_block = _mm256_set_epi64x(0, 0, 0, 0x01010040UL);
  ALIGN(64) uint8_t buffer[BLAKE2B_BLOCKBYTES];
  __m256i a = XOR(LOAD(&blake2b_IV[0]), parameter_block);
  __m256i b = LOAD(&blake2b_IV[4]);
  uint64_t counter = 0;
  do {
    const uint64_t flag = (inlen <= BLAKE2B_BLOCKBYTES) ? -1 : 0;
    size_t block_size = BLAKE2B_BLOCKBYTES;
    if(inlen < BLAKE2B_BLOCKBYTES) {
      memcpy(buffer, in, inlen);
      memset(buffer + inlen, 0, BLAKE2B_BLOCKBYTES - inlen);
      block_size = inlen;
      in = buffer;
    }
    counter += block_size;
    BLAKE2B_COMPRESS_V1(a, b, in, counter, 0, flag, 0);
    inlen -= block_size;
    in    += block_size;
  } while(inlen > 0);

  STOREU(out +  0, a);
  STOREU(out + 32, b);
  return 0;
}

#if defined(SUPERCOP)
int crypto_hash(unsigned char *out, const unsigned char *in, unsigned long long inlen) {
  return blake2b(out, in, (size_t)inlen);
}
#endif


#if defined(BLAKE2B_SELFTEST)
#include "blake2-kat.h"
#include <stdio.h>
int main(void) {
  uint8_t buf[BLAKE2_KAT_LENGTH];
  unsigned long i;

  for(i = 0; i < BLAKE2_KAT_LENGTH; ++i) {
    buf[i] = i;
  }

  for(i = 0; i < BLAKE2_KAT_LENGTH; ++i) {
    uint8_t hash[BLAKE2B_OUTBYTES];
    blake2b( hash, buf, i );

    if(0 != memcmp( hash, blake2b_kat[i], BLAKE2B_OUTBYTES )) {
      printf( "error at %lu", i );
      return -1;
    }
  }

  puts( "ok" );
  return 0;
}
#endif
