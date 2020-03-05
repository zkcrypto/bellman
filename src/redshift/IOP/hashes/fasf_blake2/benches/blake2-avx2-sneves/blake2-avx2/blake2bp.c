#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "blake2.h"
#include "blake2bp.h"
#include "blake2b-common.h"

ALIGN(64) static const uint64_t blake2b_IV[8] = {
  UINT64_C(0x6A09E667F3BCC908), UINT64_C(0xBB67AE8584CAA73B),
  UINT64_C(0x3C6EF372FE94F82B), UINT64_C(0xA54FF53A5F1D36F1),
  UINT64_C(0x510E527FADE682D1), UINT64_C(0x9B05688C2B3E6C1F),
  UINT64_C(0x1F83D9ABFB41BD6B), UINT64_C(0x5BE0CD19137E2179),
};

ALIGN(64) static const uint32_t blake2b_sigma[12][16] = {
  {  0,  32,  64,  96, 128, 160, 192, 224, 256, 288, 320, 352, 384, 416, 448, 480},
  {448, 320, 128, 256, 288, 480, 416, 192,  32, 384,   0,  64, 352, 224, 160,  96},
  {352, 256, 384,   0, 160,  64, 480, 416, 320, 448,  96, 192, 224,  32, 288, 128},
  {224, 288,  96,  32, 416, 384, 352, 448,  64, 192, 160, 320, 128,   0, 480, 256},
  {288,   0, 160, 224,  64, 128, 320, 480, 448,  32, 352, 384, 192, 256,  96, 416},
  { 64, 384, 192, 320,   0, 352, 256,  96, 128, 416, 224, 160, 480, 448,  32, 288},
  {384, 160,  32, 480, 448, 416, 128, 320,   0, 224, 192,  96, 288,  64, 256, 352},
  {416, 352, 224, 448, 384,  32,  96, 288, 160,   0, 480, 128, 256, 192,  64, 320},
  {192, 480, 448, 288, 352,  96,   0, 256, 384,  64, 416, 224,  32, 128, 320, 160},
  {320,  64, 256, 128, 224, 192,  32, 160, 480, 352, 288, 448,  96, 384, 416,   0},
  {  0,  32,  64,  96, 128, 160, 192, 224, 256, 288, 320, 352, 384, 416, 448, 480},
  {448, 320, 128, 256, 288, 480, 416, 192,  32, 384,   0,  64, 352, 224, 160,  96},
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

/* Compute root node hash; exactly 2 compressions */
static int blake2b_root(uint8_t * out, const uint8_t in[4 * BLAKE2B_OUTBYTES]) {
  const __m256i parameter_block = _mm256_set_epi64x(0, 0x00004001UL, 0, 0x02040040UL);
  __m256i a = XOR(LOAD(&blake2b_IV[0]), parameter_block);
  __m256i b = LOAD(&blake2b_IV[4]);

  BLAKE2B_COMPRESS_V1(a, b, in +   0, 128,  0,  0,  0);
  BLAKE2B_COMPRESS_V1(a, b, in + 128, 256,  0, -1, -1);

  STOREU(out +  0, a);
  STOREU(out + 32, b);
  return 0;
}

#if 0
#define BLAKE2B_G_V4(m, r, i, a, b, c, d) do {                       \
  a = ADD(a, LOAD((uint8_t const *)(m) + blake2b_sigma[r][2*i+0]));  \
  a = ADD(a, b); d = XOR(d, a); d = ROT32(d);                        \
  c = ADD(c, d); b = XOR(b, c); b = ROT24(b);                        \
  a = ADD(a, LOAD((uint8_t const *)(m) + blake2b_sigma[r][2*i+1]));  \
  a = ADD(a, b); d = XOR(d, a); d = ROT16(d);                        \
  c = ADD(c, d); b = XOR(b, c); b = ROT63(b);                        \
} while(0)

#define BLAKE2B_ROUND_V4(v, m, r) do {                \
  BLAKE2B_G_V4(m, r, 0, v[ 0], v[ 4], v[ 8], v[12]);  \
  BLAKE2B_G_V4(m, r, 1, v[ 1], v[ 5], v[ 9], v[13]);  \
  BLAKE2B_G_V4(m, r, 2, v[ 2], v[ 6], v[10], v[14]);  \
  BLAKE2B_G_V4(m, r, 3, v[ 3], v[ 7], v[11], v[15]);  \
  BLAKE2B_G_V4(m, r, 4, v[ 0], v[ 5], v[10], v[15]);  \
  BLAKE2B_G_V4(m, r, 5, v[ 1], v[ 6], v[11], v[12]);  \
  BLAKE2B_G_V4(m, r, 6, v[ 2], v[ 7], v[ 8], v[13]);  \
  BLAKE2B_G_V4(m, r, 7, v[ 3], v[ 4], v[ 9], v[14]);  \
} while(0)
#else
#define BLAKE2B_ROUND_V4(v, m, r) do {                                        \
  v[0] = ADD(v[0], LOAD((uint8_t const *)(m) + blake2b_sigma[r][2 * 0 + 0])); \
  v[1] = ADD(v[1], LOAD((uint8_t const *)(m) + blake2b_sigma[r][2 * 1 + 0])); \
  v[2] = ADD(v[2], LOAD((uint8_t const *)(m) + blake2b_sigma[r][2 * 2 + 0])); \
  v[3] = ADD(v[3], LOAD((uint8_t const *)(m) + blake2b_sigma[r][2 * 3 + 0])); \
  v[0] = ADD(v[0], v[4]);                                                     \
  v[1] = ADD(v[1], v[5]);                                                     \
  v[2] = ADD(v[2], v[6]);                                                     \
  v[3] = ADD(v[3], v[7]);                                                     \
  v[12] = XOR(v[12], v[0]);                                                   \
  v[13] = XOR(v[13], v[1]);                                                   \
  v[14] = XOR(v[14], v[2]);                                                   \
  v[15] = XOR(v[15], v[3]);                                                   \
  v[12] = ROT32(v[12]);                                                       \
  v[13] = ROT32(v[13]);                                                       \
  v[14] = ROT32(v[14]);                                                       \
  v[15] = ROT32(v[15]);                                                       \
  v[8] = ADD(v[8], v[12]);                                                    \
  v[9] = ADD(v[9], v[13]);                                                    \
  v[10] = ADD(v[10], v[14]);                                                  \
  v[11] = ADD(v[11], v[15]);                                                  \
  v[4] = XOR(v[4], v[8]);                                                     \
  v[5] = XOR(v[5], v[9]);                                                     \
  v[6] = XOR(v[6], v[10]);                                                    \
  v[7] = XOR(v[7], v[11]);                                                    \
  v[4] = ROT24(v[4]);                                                         \
  v[5] = ROT24(v[5]);                                                         \
  v[6] = ROT24(v[6]);                                                         \
  v[7] = ROT24(v[7]);                                                         \
  v[0] = ADD(v[0], LOAD((uint8_t const *)(m) + blake2b_sigma[r][2 * 0 + 1])); \
  v[1] = ADD(v[1], LOAD((uint8_t const *)(m) + blake2b_sigma[r][2 * 1 + 1])); \
  v[2] = ADD(v[2], LOAD((uint8_t const *)(m) + blake2b_sigma[r][2 * 2 + 1])); \
  v[3] = ADD(v[3], LOAD((uint8_t const *)(m) + blake2b_sigma[r][2 * 3 + 1])); \
  v[0] = ADD(v[0], v[4]);                                                     \
  v[1] = ADD(v[1], v[5]);                                                     \
  v[2] = ADD(v[2], v[6]);                                                     \
  v[3] = ADD(v[3], v[7]);                                                     \
  v[12] = XOR(v[12], v[0]);                                                   \
  v[13] = XOR(v[13], v[1]);                                                   \
  v[14] = XOR(v[14], v[2]);                                                   \
  v[15] = XOR(v[15], v[3]);                                                   \
  v[12] = ROT16(v[12]);                                                       \
  v[13] = ROT16(v[13]);                                                       \
  v[14] = ROT16(v[14]);                                                       \
  v[15] = ROT16(v[15]);                                                       \
  v[8] = ADD(v[8], v[12]);                                                    \
  v[9] = ADD(v[9], v[13]);                                                    \
  v[10] = ADD(v[10], v[14]);                                                  \
  v[11] = ADD(v[11], v[15]);                                                  \
  v[4] = XOR(v[4], v[8]);                                                     \
  v[5] = XOR(v[5], v[9]);                                                     \
  v[6] = XOR(v[6], v[10]);                                                    \
  v[7] = XOR(v[7], v[11]);                                                    \
  v[4] = ROT63(v[4]);                                                         \
  v[5] = ROT63(v[5]);                                                         \
  v[6] = ROT63(v[6]);                                                         \
  v[7] = ROT63(v[7]);                                                         \
                                                                              \
  v[0] = ADD(v[0], LOAD((uint8_t const *)(m) + blake2b_sigma[r][2 * 4 + 0])); \
  v[1] = ADD(v[1], LOAD((uint8_t const *)(m) + blake2b_sigma[r][2 * 5 + 0])); \
  v[2] = ADD(v[2], LOAD((uint8_t const *)(m) + blake2b_sigma[r][2 * 6 + 0])); \
  v[3] = ADD(v[3], LOAD((uint8_t const *)(m) + blake2b_sigma[r][2 * 7 + 0])); \
  v[0] = ADD(v[0], v[5]);                                                     \
  v[1] = ADD(v[1], v[6]);                                                     \
  v[2] = ADD(v[2], v[7]);                                                     \
  v[3] = ADD(v[3], v[4]);                                                     \
  v[15] = XOR(v[15], v[0]);                                                   \
  v[12] = XOR(v[12], v[1]);                                                   \
  v[13] = XOR(v[13], v[2]);                                                   \
  v[14] = XOR(v[14], v[3]);                                                   \
  v[15] = ROT32(v[15]);                                                       \
  v[12] = ROT32(v[12]);                                                       \
  v[13] = ROT32(v[13]);                                                       \
  v[14] = ROT32(v[14]);                                                       \
  v[10] = ADD(v[10], v[15]);                                                  \
  v[11] = ADD(v[11], v[12]);                                                  \
  v[8] = ADD(v[8], v[13]);                                                    \
  v[9] = ADD(v[9], v[14]);                                                    \
  v[5] = XOR(v[5], v[10]);                                                    \
  v[6] = XOR(v[6], v[11]);                                                    \
  v[7] = XOR(v[7], v[8]);                                                     \
  v[4] = XOR(v[4], v[9]);                                                     \
  v[5] = ROT24(v[5]);                                                         \
  v[6] = ROT24(v[6]);                                                         \
  v[7] = ROT24(v[7]);                                                         \
  v[4] = ROT24(v[4]);                                                         \
  v[0] = ADD(v[0], LOAD((uint8_t const *)(m) + blake2b_sigma[r][2 * 4 + 1])); \
  v[1] = ADD(v[1], LOAD((uint8_t const *)(m) + blake2b_sigma[r][2 * 5 + 1])); \
  v[2] = ADD(v[2], LOAD((uint8_t const *)(m) + blake2b_sigma[r][2 * 6 + 1])); \
  v[3] = ADD(v[3], LOAD((uint8_t const *)(m) + blake2b_sigma[r][2 * 7 + 1])); \
  v[0] = ADD(v[0], v[5]);                                                     \
  v[1] = ADD(v[1], v[6]);                                                     \
  v[2] = ADD(v[2], v[7]);                                                     \
  v[3] = ADD(v[3], v[4]);                                                     \
  v[15] = XOR(v[15], v[0]);                                                   \
  v[12] = XOR(v[12], v[1]);                                                   \
  v[13] = XOR(v[13], v[2]);                                                   \
  v[14] = XOR(v[14], v[3]);                                                   \
  v[15] = ROT16(v[15]);                                                       \
  v[12] = ROT16(v[12]);                                                       \
  v[13] = ROT16(v[13]);                                                       \
  v[14] = ROT16(v[14]);                                                       \
  v[10] = ADD(v[10], v[15]);                                                  \
  v[11] = ADD(v[11], v[12]);                                                  \
  v[8] = ADD(v[8], v[13]);                                                    \
  v[9] = ADD(v[9], v[14]);                                                    \
  v[5] = XOR(v[5], v[10]);                                                    \
  v[6] = XOR(v[6], v[11]);                                                    \
  v[7] = XOR(v[7], v[8]);                                                     \
  v[4] = XOR(v[4], v[9]);                                                     \
  v[5] = ROT63(v[5]);                                                         \
  v[6] = ROT63(v[6]);                                                         \
  v[7] = ROT63(v[7]);                                                         \
  v[4] = ROT63(v[4]);                                                         \
} while (0)
#endif

#if defined(PERMUTE_WITH_GATHER)
#define BLAKE2B_LOADMSG_V4(w, m) do {             \
  int i;                                          \
  for(i = 0; i < 16; ++i) {                       \
    w[i] = _mm256_i32gather_epi64(                \
      (const void *)((m) + i * sizeof(uint64_t)), \
      _mm_set_epi32(48, 32, 16, 0),               \
      sizeof(uint64_t)                            \
    );                                            \
  }                                               \
} while(0)
#else
#define BLAKE2B_PACK_MSG_V4(w, m) do {              \
  __m256i t0, t1, t2, t3;                           \
  t0 = _mm256_unpacklo_epi64(m[ 0], m[ 4]);         \
  t1 = _mm256_unpackhi_epi64(m[ 0], m[ 4]);         \
  t2 = _mm256_unpacklo_epi64(m[ 8], m[12]);         \
  t3 = _mm256_unpackhi_epi64(m[ 8], m[12]);         \
  w[ 0] = _mm256_permute2x128_si256(t0, t2, 0x20);  \
  w[ 2] = _mm256_permute2x128_si256(t0, t2, 0x31);  \
  w[ 1] = _mm256_permute2x128_si256(t1, t3, 0x20);  \
  w[ 3] = _mm256_permute2x128_si256(t1, t3, 0x31);  \
  t0 = _mm256_unpacklo_epi64(m[ 1], m[ 5]);         \
  t1 = _mm256_unpackhi_epi64(m[ 1], m[ 5]);         \
  t2 = _mm256_unpacklo_epi64(m[ 9], m[13]);         \
  t3 = _mm256_unpackhi_epi64(m[ 9], m[13]);         \
  w[ 4] = _mm256_permute2x128_si256(t0, t2, 0x20);  \
  w[ 6] = _mm256_permute2x128_si256(t0, t2, 0x31);  \
  w[ 5] = _mm256_permute2x128_si256(t1, t3, 0x20);  \
  w[ 7] = _mm256_permute2x128_si256(t1, t3, 0x31);  \
  t0 = _mm256_unpacklo_epi64(m[ 2], m[ 6]);         \
  t1 = _mm256_unpackhi_epi64(m[ 2], m[ 6]);         \
  t2 = _mm256_unpacklo_epi64(m[10], m[14]);         \
  t3 = _mm256_unpackhi_epi64(m[10], m[14]);         \
  w[ 8] = _mm256_permute2x128_si256(t0, t2, 0x20);  \
  w[10] = _mm256_permute2x128_si256(t0, t2, 0x31);  \
  w[ 9] = _mm256_permute2x128_si256(t1, t3, 0x20);  \
  w[11] = _mm256_permute2x128_si256(t1, t3, 0x31);  \
  t0 = _mm256_unpacklo_epi64(m[ 3], m[ 7]);         \
  t1 = _mm256_unpackhi_epi64(m[ 3], m[ 7]);         \
  t2 = _mm256_unpacklo_epi64(m[11], m[15]);         \
  t3 = _mm256_unpackhi_epi64(m[11], m[15]);         \
  w[12] = _mm256_permute2x128_si256(t0, t2, 0x20);  \
  w[14] = _mm256_permute2x128_si256(t0, t2, 0x31);  \
  w[13] = _mm256_permute2x128_si256(t1, t3, 0x20);  \
  w[15] = _mm256_permute2x128_si256(t1, t3, 0x31);  \
} while(0)

#define BLAKE2B_LOADMSG_V4(w, m) do { \
  __m256i t[16];                      \
  int i;                              \
  for(i = 0; i < 16; ++i) {           \
    t[i] = LOADU((m) + i * 32);       \
  }                                   \
  BLAKE2B_PACK_MSG_V4(w, t);          \
} while(0)
#endif

#define BLAKE2B_UNPACK_STATE_V4(u, v) do {         \
  __m256i t0, t1, t2, t3;                          \
  t0 = _mm256_unpacklo_epi64(v[0], v[1]);          \
  t1 = _mm256_unpackhi_epi64(v[0], v[1]);          \
  t2 = _mm256_unpacklo_epi64(v[2], v[3]);          \
  t3 = _mm256_unpackhi_epi64(v[2], v[3]);          \
  u[0] = _mm256_permute2x128_si256(t0, t2, 0x20);  \
  u[2] = _mm256_permute2x128_si256(t1, t3, 0x20);  \
  u[4] = _mm256_permute2x128_si256(t0, t2, 0x31);  \
  u[6] = _mm256_permute2x128_si256(t1, t3, 0x31);  \
  t0 = _mm256_unpacklo_epi64(v[4], v[5]);          \
  t1 = _mm256_unpackhi_epi64(v[4], v[5]);          \
  t2 = _mm256_unpacklo_epi64(v[6], v[7]);          \
  t3 = _mm256_unpackhi_epi64(v[6], v[7]);          \
  u[1] = _mm256_permute2x128_si256(t0, t2, 0x20);  \
  u[3] = _mm256_permute2x128_si256(t1, t3, 0x20);  \
  u[5] = _mm256_permute2x128_si256(t0, t2, 0x31);  \
  u[7] = _mm256_permute2x128_si256(t1, t3, 0x31);  \
} while(0)

#define BLAKE2B_COMPRESS_V4(v, m, counter, flag) do {                   \
  const __m256i flag_mask = _mm256_set_epi64x(-1, 0, 0, 0);             \
  __m256i iv[8], w[16];                                                 \
  int i, r;                                                             \
  for(i = 0; i < 8; ++i) {                                              \
    iv[i] = v[i];                                                       \
  }                                                                     \
  v[ 8] = _mm256_set1_epi64x(blake2b_IV[0]);                            \
  v[ 9] = _mm256_set1_epi64x(blake2b_IV[1]);                            \
  v[10] = _mm256_set1_epi64x(blake2b_IV[2]);                            \
  v[11] = _mm256_set1_epi64x(blake2b_IV[3]);                            \
  v[12] = XOR(_mm256_set1_epi64x(blake2b_IV[4]), counter);              \
  v[13] = _mm256_set1_epi64x(blake2b_IV[5]);                            \
  v[14] = XOR(_mm256_set1_epi64x(blake2b_IV[6]), flag);                 \
  v[15] = XOR(_mm256_set1_epi64x(blake2b_IV[7]), AND(flag, flag_mask)); \
  BLAKE2B_LOADMSG_V4(w, m);                                             \
  for(r = 0; r < 12; ++r) {                                             \
    BLAKE2B_ROUND_V4(v, w, r);                                          \
  }                                                                     \
  for(i = 0; i < 8; ++i) {                                              \
    v[i] = XOR(XOR(v[i], v[i+8]), iv[i]);                               \
  }                                                                     \
} while(0)


int blake2bp(uint8_t * out, const uint8_t * in, size_t inlen) {
  ALIGN(64) uint8_t buffer[4 * BLAKE2B_BLOCKBYTES];
  __m256i v[16], s[8];
  union {
    __m256i  v;
    uint64_t w[4];
  } counter;
  int i, lane;

  for(i = 0; i < 8; ++i) {
    v[i] = _mm256_set1_epi64x(blake2b_IV[i]);
  }

  v[0] = XOR(v[0], _mm256_set1_epi64x(0x02040040UL));
  v[1] = XOR(v[1], _mm256_set_epi64x(3, 2, 1, 0));
  v[2] = XOR(v[2], _mm256_set1_epi64x(0x00004000UL));

  counter.v = _mm256_setzero_si256();
  do {
    size_t block_size = 4 * BLAKE2B_BLOCKBYTES;
    const uint8_t * ptr = in;
    __m256i x0, x1, x2, x3, x4, f0;

    const __m256i c0 = _mm256_set_epi64x(384, 256, 128, 0);
    const __m256i c1 = _mm256_set_epi64x(512+384+1, 512+256+1, 512+128+1, 512+1);
    const __m256i c2 = _mm256_setzero_si256();
    const __m256i c3 = _mm256_set1_epi64x(128);

    if(inlen < block_size) {
      memcpy(buffer, in, inlen);
      memset(buffer + inlen, 0, 4 * BLAKE2B_BLOCKBYTES - inlen);
      block_size = inlen;
      ptr = buffer;
    }

    x0 = _mm256_set1_epi64x(inlen);
    x1 = _mm256_cmpgt_epi64(x0, c0);
    x2 = _mm256_blendv_epi8(c2, _mm256_sub_epi64(x0, c0), x1);
    x3 = _mm256_cmpgt_epi64(x2, c3);
    x4 = _mm256_blendv_epi8(x2, c3, x3);
    f0 = _mm256_cmpgt_epi64(c1, x0);

    counter.v  = _mm256_add_epi64(counter.v, x4);

    BLAKE2B_COMPRESS_V4(v, ptr, counter.v, f0);
    in    += block_size;
    inlen -= block_size;
  } while(inlen >= 4 * BLAKE2B_BLOCKBYTES);

  BLAKE2B_UNPACK_STATE_V4(s, v);

  for(lane = 0; lane < 4; ++lane) {
    size_t block_size = BLAKE2B_BLOCKBYTES;
    const uint8_t * ptr = in;
    if(!inlen) break;
    if(inlen < block_size) {
      memcpy(buffer, in, inlen);
      memset(buffer + inlen, 0, BLAKE2B_BLOCKBYTES - inlen);
      block_size = inlen;
      ptr = buffer;
    }
    counter.w[lane] += block_size;
    BLAKE2B_COMPRESS_V1(s[lane*2+0], s[lane*2+1], ptr, counter.w[lane], 0, -1, -(lane == 3));
    in    += block_size;
    inlen -= block_size;
  }
  return blake2b_root(out, (void *)s);
}

#if defined(SUPERCOP)
int crypto_hash(unsigned char *out, const unsigned char *in, unsigned long long inlen) {
  return blake2bp(out, in, (size_t)inlen);
}
#endif

#if defined(BLAKE2BP_SELFTEST)
#include "blake2-kat.h"
#include <stdio.h>
int main(void) {
  uint8_t buf[BLAKE2_KAT_LENGTH];
  unsigned long i;

  for( i = 0; i < BLAKE2_KAT_LENGTH; ++i ) {
    buf[i] = i;
  }

  for( i = 0; i < BLAKE2_KAT_LENGTH; ++i ) {
    uint8_t hash[BLAKE2B_OUTBYTES];
    blake2bp( hash, buf, i );

    if( 0 != memcmp( hash, blake2bp_kat[i], BLAKE2B_OUTBYTES ) ) {
      printf( "error at %lu", i );
      return -1;
    }
  }

  puts( "ok" );
  return 0;
}
#endif
