#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#include "blake2.h"
#include "blake2sp.h"
#include "blake2s-common.h"

#include <immintrin.h>

ALIGN(64) static const uint32_t blake2s_IV[8] = {
  UINT32_C(0x6A09E667), UINT32_C(0xBB67AE85),
  UINT32_C(0x3C6EF372), UINT32_C(0xA54FF53A),
  UINT32_C(0x510E527F), UINT32_C(0x9B05688C),
  UINT32_C(0x1F83D9AB), UINT32_C(0x5BE0CD19)
};

ALIGN(64) static const uint32_t blake2s_sigma[10][16] = {
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
};

#define BLAKE2S_G1_V1(a, b, c, d, m) do {              \
  a = ADD128(a, m);                                    \
  a = ADD128(a, b); d = XOR128(d, a); d = ROT16128(d); \
  c = ADD128(c, d); b = XOR128(b, c); b = ROT12128(b); \
} while(0)

#define BLAKE2S_G2_V1(a, b, c, d, m) do {             \
  a = ADD128(a, m);                                   \
  a = ADD128(a, b); d = XOR128(d, a); d = ROT8128(d); \
  c = ADD128(c, d); b = XOR128(b, c); b = ROT7128(b); \
} while(0)

#define BLAKE2S_DIAG_V1(a, b, c, d) do {          \
  d = _mm_shuffle_epi32(d, _MM_SHUFFLE(2,1,0,3)); \
  c = _mm_shuffle_epi32(c, _MM_SHUFFLE(1,0,3,2)); \
  b = _mm_shuffle_epi32(b, _MM_SHUFFLE(0,3,2,1)); \
} while(0)

#define BLAKE2S_UNDIAG_V1(a, b, c, d) do {        \
  d = _mm_shuffle_epi32(d, _MM_SHUFFLE(0,3,2,1)); \
  c = _mm_shuffle_epi32(c, _MM_SHUFFLE(1,0,3,2)); \
  b = _mm_shuffle_epi32(b, _MM_SHUFFLE(2,1,0,3)); \
} while(0)

#if defined(PERMUTE_WITH_SHUFFLES)
  #include "blake2s-load-sse41.h"
#elif defined(PERMUTE_WITH_GATHER)
#else
  #include "blake2s-load-sse2.h"
#endif

#if defined(PERMUTE_WITH_GATHER)
ALIGN(64) static const uint32_t indices[12][16] = {
  { 0,  2,  4,  6, 1,  3,  5,  7, 8, 10, 12, 14, 9, 11, 13, 15},
  {14,  4,  9, 13,10,  8, 15,  6, 1,  0, 11,  5,12,  2,  7,  3},
  {11, 12,  5, 15, 8,  0,  2, 13,10,  3,  7,  9,14,  6,  1,  4},
  { 7,  3, 13, 11, 9,  1, 12, 14, 2,  5,  4, 15, 6, 10,  0,  8},
  { 9,  5,  2, 10, 0,  7,  4, 15,14, 11,  6,  3, 1, 12,  8, 13},
  { 2,  6,  0,  8,12, 10, 11,  3, 4,  7, 15,  1,13,  5, 14,  9},
  {12,  1, 14,  4, 5, 15, 13, 10, 0,  6,  9,  8, 7,  3,  2, 11},
  {13,  7, 12,  3,11, 14,  1,  9, 5, 15,  8,  2, 0,  4,  6, 10},
  { 6, 14, 11,  0,15,  9,  3,  8,12, 13,  1, 10, 2,  7,  4,  5},
  {10,  8,  7,  1, 2,  4,  6,  5,15,  9,  3, 13,11, 14, 12,  0},
  { 0,  2,  4,  6, 1,  3,  5,  7, 8, 10, 12, 14, 9, 11, 13, 15},
  {14,  4,  9, 13,10,  8, 15,  6, 1,  0, 11,  5,12,  2,  7,  3},
};

#define BLAKE2S_ROUND_V1(a, b, c, d, r, m) do {                           \
  __m128i b0;                                                             \
  b0 = _mm_i32gather_epi32((void *)(m), LOAD128(&indices[r][ 0]), 4);     \
  BLAKE2S_G1_V1(a, b, c, d, b0);                                          \
  b0 = _mm_i32gather_epi32((void *)(m), LOAD128(&indices[r][ 4]), 4);     \
  BLAKE2S_G2_V1(a, b, c, d, b0);                                          \
  BLAKE2S_DIAG_V1(a, b, c, d);                                            \
  b0 = _mm_i32gather_epi32((void *)(m), LOAD128(&indices[r][ 8]), 4);     \
  BLAKE2S_G1_V1(a, b, c, d, b0);                                          \
  b0 = _mm_i32gather_epi32((void *)(m), LOAD128(&indices[r][12]), 4);     \
  BLAKE2S_G2_V1(a, b, c, d, b0);                                          \
  BLAKE2S_UNDIAG_V1(a, b, c, d);                                          \
} while(0)

#define BLAKE2S_ROUNDS_V1(a, b, c, d, m) do { \
  int i;                                      \
  for(i = 0; i < 10; ++i) {                   \
    BLAKE2S_ROUND_V1(a, b, c, d, i, m);       \
  }                                           \
} while(0)
#else /* !PERMUTE_WITH_GATHER */
#define BLAKE2S_ROUND_V1(a, b, c, d, r, m) do { \
  __m128i b0;                                   \
  BLAKE2S_LOAD_MSG_ ##r ##_1(b0);               \
  BLAKE2S_G1_V1(a, b, c, d, b0);                \
  BLAKE2S_LOAD_MSG_ ##r ##_2(b0);               \
  BLAKE2S_G2_V1(a, b, c, d, b0);                \
  BLAKE2S_DIAG_V1(a, b, c, d);                  \
  BLAKE2S_LOAD_MSG_ ##r ##_3(b0);               \
  BLAKE2S_G1_V1(a, b, c, d, b0);                \
  BLAKE2S_LOAD_MSG_ ##r ##_4(b0);               \
  BLAKE2S_G2_V1(a, b, c, d, b0);                \
  BLAKE2S_UNDIAG_V1(a, b, c, d);                \
} while(0)

#define BLAKE2S_ROUNDS_V1(a, b, c, d, m) do {   \
  BLAKE2S_ROUND_V1(a, b, c, d,  0, (m));        \
  BLAKE2S_ROUND_V1(a, b, c, d,  1, (m));        \
  BLAKE2S_ROUND_V1(a, b, c, d,  2, (m));        \
  BLAKE2S_ROUND_V1(a, b, c, d,  3, (m));        \
  BLAKE2S_ROUND_V1(a, b, c, d,  4, (m));        \
  BLAKE2S_ROUND_V1(a, b, c, d,  5, (m));        \
  BLAKE2S_ROUND_V1(a, b, c, d,  6, (m));        \
  BLAKE2S_ROUND_V1(a, b, c, d,  7, (m));        \
  BLAKE2S_ROUND_V1(a, b, c, d,  8, (m));        \
  BLAKE2S_ROUND_V1(a, b, c, d,  9, (m));        \
} while(0)
#endif

#if defined(PERMUTE_WITH_GATHER)
#define DECLARE_MESSAGE_WORDS(m)
#elif defined(PERMUTE_WITH_SHUFFLES)
#define DECLARE_MESSAGE_WORDS(m)           \
  const __m128i m0 = LOADU128( (m) + 00 ); \
  const __m128i m1 = LOADU128( (m) + 16 ); \
  const __m128i m2 = LOADU128( (m) + 32 ); \
  const __m128i m3 = LOADU128( (m) + 48 ); \
  __m128i t0, t1, t2;
#else
#define DECLARE_MESSAGE_WORDS(m)           \
  const uint32_t  m0 = LOADU32((m) +   0); \
  const uint32_t  m1 = LOADU32((m) +   4); \
  const uint32_t  m2 = LOADU32((m) +   8); \
  const uint32_t  m3 = LOADU32((m) +  12); \
  const uint32_t  m4 = LOADU32((m) +  16); \
  const uint32_t  m5 = LOADU32((m) +  20); \
  const uint32_t  m6 = LOADU32((m) +  24); \
  const uint32_t  m7 = LOADU32((m) +  28); \
  const uint32_t  m8 = LOADU32((m) +  32); \
  const uint32_t  m9 = LOADU32((m) +  36); \
  const uint32_t m10 = LOADU32((m) +  40); \
  const uint32_t m11 = LOADU32((m) +  44); \
  const uint32_t m12 = LOADU32((m) +  48); \
  const uint32_t m13 = LOADU32((m) +  52); \
  const uint32_t m14 = LOADU32((m) +  56); \
  const uint32_t m15 = LOADU32((m) +  60);
#endif

#define BLAKE2S_COMPRESS_V1(a, b, m, t0, t1, f0, f1) do { \
  DECLARE_MESSAGE_WORDS(m)                                \
  const __m128i iv0 = a;                                  \
  const __m128i iv1 = b;                                  \
  __m128i c = LOAD128(&blake2s_IV[0]);                    \
  __m128i d = XOR128(                                     \
    LOAD128(&blake2s_IV[4]),                              \
    _mm_set_epi32(f1, f0, t1, t0)                         \
  );                                                      \
  BLAKE2S_ROUNDS_V1(a, b, c, d, m);                       \
  a = XOR128(a, c);                                       \
  b = XOR128(b, d);                                       \
  a = XOR128(a, iv0);                                     \
  b = XOR128(b, iv1);                                     \
} while(0)

/*
static int blake2s(uint8_t * out, const uint8_t * in, size_t inlen) {
  const __m128i parameter_block = _mm_set_epi32(0, 0, 0, 0x01010020UL);
  ALIGN(64) uint8_t buffer[BLAKE2S_BLOCKBYTES];
  __m128i a = XOR128(LOAD128(&blake2s_IV[0]), parameter_block);
  __m128i b = LOAD128(&blake2s_IV[4]);

  uint64_t counter = 0;
  do {
    const uint64_t flag = (inlen <= BLAKE2S_BLOCKBYTES) ? -1 : 0;
    size_t block_size = BLAKE2S_BLOCKBYTES;
    if(inlen < BLAKE2S_BLOCKBYTES) {
      memcpy(buffer, in, inlen);
      memset(buffer + inlen, 0, BLAKE2S_BLOCKBYTES - inlen);
      block_size = inlen;
      in = buffer;
    }
    counter += block_size;
    BLAKE2S_COMPRESS_V1(a, b, in, (counter & 0xFFFFFFFF), (counter >> 32), flag, 0);
    inlen -= block_size;
    in    += block_size;
  } while(inlen > 0);

  STOREU128(out +  0, a);
  STOREU128(out + 16, b);
  return 0;
}
*/

/* Compute root node hash; exactly 4 compressions */
static int blake2s_root(uint8_t * out, const uint8_t in[8 * BLAKE2S_OUTBYTES]) {
  const __m128i parameter_block = _mm_set_epi32(0x20010000, 0, 0, 0x02080020UL);
  __m128i a = XOR128(LOAD128(&blake2s_IV[0]), parameter_block);
  __m128i b = LOAD128(&blake2s_IV[4]);
  int i;
  for(i = 0; i < 4; ++i) {
    const uint64_t counter = BLAKE2S_BLOCKBYTES * (i + 1);
    const uint32_t flag    = (i == 3) ? -1 : 0;
    BLAKE2S_COMPRESS_V1(a, b, in, (counter & 0xFFFFFFFF), (counter >> 32), flag, flag);
    in += BLAKE2S_BLOCKBYTES;
  }
  STOREU128(out +  0, a);
  STOREU128(out + 16, b);
  return 0;
}

#if 0
#define BLAKE2S_G_V8(m, r, i, a, b, c, d) do {                       \
  a = ADD(a, LOAD((uint8_t const *)(m) + blake2s_sigma[r][2*i+0]));  \
  a = ADD(a, b); d = XOR(d, a); d = ROT16(d);                        \
  c = ADD(c, d); b = XOR(b, c); b = ROT12(b);                        \
  a = ADD(a, LOAD((uint8_t const *)(m) + blake2s_sigma[r][2*i+1]));  \
  a = ADD(a, b); d = XOR(d, a); d = ROT8(d);                         \
  c = ADD(c, d); b = XOR(b, c); b = ROT7(b);                         \
} while(0)

#define BLAKE2S_ROUND_V8(v, m, r) do {                \
  BLAKE2S_G_V8(m, r, 0, v[ 0], v[ 4], v[ 8], v[12]);  \
  BLAKE2S_G_V8(m, r, 1, v[ 1], v[ 5], v[ 9], v[13]);  \
  BLAKE2S_G_V8(m, r, 2, v[ 2], v[ 6], v[10], v[14]);  \
  BLAKE2S_G_V8(m, r, 3, v[ 3], v[ 7], v[11], v[15]);  \
  BLAKE2S_G_V8(m, r, 4, v[ 0], v[ 5], v[10], v[15]);  \
  BLAKE2S_G_V8(m, r, 5, v[ 1], v[ 6], v[11], v[12]);  \
  BLAKE2S_G_V8(m, r, 6, v[ 2], v[ 7], v[ 8], v[13]);  \
  BLAKE2S_G_V8(m, r, 7, v[ 3], v[ 4], v[ 9], v[14]);  \
} while(0)
#else
#define BLAKE2S_ROUND_V8(v, m, r) do {                                        \
  v[0] = ADD(v[0], LOAD((uint8_t const *)(m) + blake2s_sigma[r][2 * 0 + 0])); \
  v[1] = ADD(v[1], LOAD((uint8_t const *)(m) + blake2s_sigma[r][2 * 1 + 0])); \
  v[2] = ADD(v[2], LOAD((uint8_t const *)(m) + blake2s_sigma[r][2 * 2 + 0])); \
  v[3] = ADD(v[3], LOAD((uint8_t const *)(m) + blake2s_sigma[r][2 * 3 + 0])); \
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
  v[4] = ROT12(v[4]);                                                         \
  v[5] = ROT12(v[5]);                                                         \
  v[6] = ROT12(v[6]);                                                         \
  v[7] = ROT12(v[7]);                                                         \
  v[0] = ADD(v[0], LOAD((uint8_t const *)(m) + blake2s_sigma[r][2 * 0 + 1])); \
  v[1] = ADD(v[1], LOAD((uint8_t const *)(m) + blake2s_sigma[r][2 * 1 + 1])); \
  v[2] = ADD(v[2], LOAD((uint8_t const *)(m) + blake2s_sigma[r][2 * 2 + 1])); \
  v[3] = ADD(v[3], LOAD((uint8_t const *)(m) + blake2s_sigma[r][2 * 3 + 1])); \
  v[0] = ADD(v[0], v[4]);                                                     \
  v[1] = ADD(v[1], v[5]);                                                     \
  v[2] = ADD(v[2], v[6]);                                                     \
  v[3] = ADD(v[3], v[7]);                                                     \
  v[12] = XOR(v[12], v[0]);                                                   \
  v[13] = XOR(v[13], v[1]);                                                   \
  v[14] = XOR(v[14], v[2]);                                                   \
  v[15] = XOR(v[15], v[3]);                                                   \
  v[12] = ROT8(v[12]);                                                        \
  v[13] = ROT8(v[13]);                                                        \
  v[14] = ROT8(v[14]);                                                        \
  v[15] = ROT8(v[15]);                                                        \
  v[8] = ADD(v[8], v[12]);                                                    \
  v[9] = ADD(v[9], v[13]);                                                    \
  v[10] = ADD(v[10], v[14]);                                                  \
  v[11] = ADD(v[11], v[15]);                                                  \
  v[4] = XOR(v[4], v[8]);                                                     \
  v[5] = XOR(v[5], v[9]);                                                     \
  v[6] = XOR(v[6], v[10]);                                                    \
  v[7] = XOR(v[7], v[11]);                                                    \
  v[4] = ROT7(v[4]);                                                          \
  v[5] = ROT7(v[5]);                                                          \
  v[6] = ROT7(v[6]);                                                          \
  v[7] = ROT7(v[7]);                                                          \
                                                                              \
  v[0] = ADD(v[0], LOAD((uint8_t const *)(m) + blake2s_sigma[r][2 * 4 + 0])); \
  v[1] = ADD(v[1], LOAD((uint8_t const *)(m) + blake2s_sigma[r][2 * 5 + 0])); \
  v[2] = ADD(v[2], LOAD((uint8_t const *)(m) + blake2s_sigma[r][2 * 6 + 0])); \
  v[3] = ADD(v[3], LOAD((uint8_t const *)(m) + blake2s_sigma[r][2 * 7 + 0])); \
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
  v[5] = ROT12(v[5]);                                                         \
  v[6] = ROT12(v[6]);                                                         \
  v[7] = ROT12(v[7]);                                                         \
  v[4] = ROT12(v[4]);                                                         \
  v[0] = ADD(v[0], LOAD((uint8_t const *)(m) + blake2s_sigma[r][2 * 4 + 1])); \
  v[1] = ADD(v[1], LOAD((uint8_t const *)(m) + blake2s_sigma[r][2 * 5 + 1])); \
  v[2] = ADD(v[2], LOAD((uint8_t const *)(m) + blake2s_sigma[r][2 * 6 + 1])); \
  v[3] = ADD(v[3], LOAD((uint8_t const *)(m) + blake2s_sigma[r][2 * 7 + 1])); \
  v[0] = ADD(v[0], v[5]);                                                     \
  v[1] = ADD(v[1], v[6]);                                                     \
  v[2] = ADD(v[2], v[7]);                                                     \
  v[3] = ADD(v[3], v[4]);                                                     \
  v[15] = XOR(v[15], v[0]);                                                   \
  v[12] = XOR(v[12], v[1]);                                                   \
  v[13] = XOR(v[13], v[2]);                                                   \
  v[14] = XOR(v[14], v[3]);                                                   \
  v[15] = ROT8(v[15]);                                                        \
  v[12] = ROT8(v[12]);                                                        \
  v[13] = ROT8(v[13]);                                                        \
  v[14] = ROT8(v[14]);                                                        \
  v[10] = ADD(v[10], v[15]);                                                  \
  v[11] = ADD(v[11], v[12]);                                                  \
  v[8] = ADD(v[8], v[13]);                                                    \
  v[9] = ADD(v[9], v[14]);                                                    \
  v[5] = XOR(v[5], v[10]);                                                    \
  v[6] = XOR(v[6], v[11]);                                                    \
  v[7] = XOR(v[7], v[8]);                                                     \
  v[4] = XOR(v[4], v[9]);                                                     \
  v[5] = ROT7(v[5]);                                                          \
  v[6] = ROT7(v[6]);                                                          \
  v[7] = ROT7(v[7]);                                                          \
  v[4] = ROT7(v[4]);                                                          \
} while (0)
#endif

#if defined(PERMUTE_WITH_GATHER)
#define BLAKE2S_LOADMSG_V8(w, m) do {                   \
  int i;                                                \
  for(i = 0; i < 16; ++i) {                             \
    w[i] = _mm256_i32gather_epi32(                      \
      (const void *)((m) + i * sizeof(uint32_t)),       \
      _mm256_set_epi32(112, 96, 80, 64, 48, 32, 16, 0), \
      sizeof(uint32_t)                                  \
    );                                                  \
  }                                                     \
} while(0)
#else

#define BLAKE2S_PACK_MSG_V8(w, m)  do {            \
  __m256i t0, t1, t2, t3, t4, t5, t6, t7;          \
  __m256i s0, s1, s2, s3;                          \
                                                   \
  t0 = _mm256_unpacklo_epi32(m[ 0], m[ 2]);        \
  t1 = _mm256_unpackhi_epi32(m[ 0], m[ 2]);        \
  t2 = _mm256_unpacklo_epi32(m[ 4], m[ 6]);        \
  t3 = _mm256_unpackhi_epi32(m[ 4], m[ 6]);        \
  t4 = _mm256_unpacklo_epi32(m[ 8], m[10]);        \
  t5 = _mm256_unpackhi_epi32(m[ 8], m[10]);        \
  t6 = _mm256_unpacklo_epi32(m[12], m[14]);        \
  t7 = _mm256_unpackhi_epi32(m[12], m[14]);        \
                                                   \
  s0 = _mm256_unpacklo_epi64(t0, t2);              \
  s1 = _mm256_unpackhi_epi64(t0, t2);              \
  s2 = _mm256_unpacklo_epi64(t4, t6);              \
  s3 = _mm256_unpackhi_epi64(t4, t6);              \
                                                   \
  w[0] = _mm256_permute2x128_si256(s0, s2, 0x20);  \
  w[4] = _mm256_permute2x128_si256(s0, s2, 0x31);  \
  w[1] = _mm256_permute2x128_si256(s1, s3, 0x20);  \
  w[5] = _mm256_permute2x128_si256(s1, s3, 0x31);  \
                                                   \
  s0 = _mm256_unpacklo_epi64(t1, t3);              \
  s1 = _mm256_unpackhi_epi64(t1, t3);              \
  s2 = _mm256_unpacklo_epi64(t5, t7);              \
  s3 = _mm256_unpackhi_epi64(t5, t7);              \
                                                   \
  w[2] = _mm256_permute2x128_si256(s0, s2, 0x20);  \
  w[6] = _mm256_permute2x128_si256(s0, s2, 0x31);  \
  w[3] = _mm256_permute2x128_si256(s1, s3, 0x20);  \
  w[7] = _mm256_permute2x128_si256(s1, s3, 0x31);  \
                                                   \
  t0 = _mm256_unpacklo_epi32(m[ 1], m[ 3]);        \
  t1 = _mm256_unpackhi_epi32(m[ 1], m[ 3]);        \
  t2 = _mm256_unpacklo_epi32(m[ 5], m[ 7]);        \
  t3 = _mm256_unpackhi_epi32(m[ 5], m[ 7]);        \
  t4 = _mm256_unpacklo_epi32(m[ 9], m[11]);        \
  t5 = _mm256_unpackhi_epi32(m[ 9], m[11]);        \
  t6 = _mm256_unpacklo_epi32(m[13], m[15]);        \
  t7 = _mm256_unpackhi_epi32(m[13], m[15]);        \
                                                   \
  s0 = _mm256_unpacklo_epi64(t0, t2);              \
  s1 = _mm256_unpackhi_epi64(t0, t2);              \
  s2 = _mm256_unpacklo_epi64(t4, t6);              \
  s3 = _mm256_unpackhi_epi64(t4, t6);              \
                                                   \
  w[ 8] = _mm256_permute2x128_si256(s0, s2, 0x20); \
  w[12] = _mm256_permute2x128_si256(s0, s2, 0x31); \
  w[ 9] = _mm256_permute2x128_si256(s1, s3, 0x20); \
  w[13] = _mm256_permute2x128_si256(s1, s3, 0x31); \
                                                   \
  s0 = _mm256_unpacklo_epi64(t1, t3);              \
  s1 = _mm256_unpackhi_epi64(t1, t3);              \
  s2 = _mm256_unpacklo_epi64(t5, t7);              \
  s3 = _mm256_unpackhi_epi64(t5, t7);              \
                                                   \
  w[10] = _mm256_permute2x128_si256(s0, s2, 0x20); \
  w[14] = _mm256_permute2x128_si256(s0, s2, 0x31); \
  w[11] = _mm256_permute2x128_si256(s1, s3, 0x20); \
  w[15] = _mm256_permute2x128_si256(s1, s3, 0x31); \
} while(0)

#define BLAKE2S_LOADMSG_V8(w, m) do { \
  __m256i t[16];                      \
  int i;                              \
  for(i = 0; i < 16; ++i) {           \
    t[i] = LOADU((m) + i * 32);       \
  }                                   \
  BLAKE2S_PACK_MSG_V8(w, t);          \
} while(0)
#endif

#define BLAKE2S_UNPACK_STATE_V8(u, v) do {        \
  __m256i t0, t1, t2, t3, t4, t5, t6, t7;         \
  __m256i s0, s1, s2, s3, s4, s5, s6, s7;         \
  t0 = _mm256_unpacklo_epi32(v[0], v[1]);         \
  t1 = _mm256_unpackhi_epi32(v[0], v[1]);         \
  t2 = _mm256_unpacklo_epi32(v[2], v[3]);         \
  t3 = _mm256_unpackhi_epi32(v[2], v[3]);         \
  t4 = _mm256_unpacklo_epi32(v[4], v[5]);         \
  t5 = _mm256_unpackhi_epi32(v[4], v[5]);         \
  t6 = _mm256_unpacklo_epi32(v[6], v[7]);         \
  t7 = _mm256_unpackhi_epi32(v[6], v[7]);         \
                                                  \
  s0 = _mm256_unpacklo_epi64(t0, t2);             \
  s1 = _mm256_unpackhi_epi64(t0, t2);             \
  s2 = _mm256_unpacklo_epi64(t1, t3);             \
  s3 = _mm256_unpackhi_epi64(t1, t3);             \
  s4 = _mm256_unpacklo_epi64(t4, t6);             \
  s5 = _mm256_unpackhi_epi64(t4, t6);             \
  s6 = _mm256_unpacklo_epi64(t5, t7);             \
  s7 = _mm256_unpackhi_epi64(t5, t7);             \
                                                  \
  u[0] = _mm256_permute2x128_si256(s0, s4, 0x20); \
  u[1] = _mm256_permute2x128_si256(s1, s5, 0x20); \
  u[2] = _mm256_permute2x128_si256(s2, s6, 0x20); \
  u[3] = _mm256_permute2x128_si256(s3, s7, 0x20); \
  u[4] = _mm256_permute2x128_si256(s0, s4, 0x31); \
  u[5] = _mm256_permute2x128_si256(s1, s5, 0x31); \
  u[6] = _mm256_permute2x128_si256(s2, s6, 0x31); \
  u[7] = _mm256_permute2x128_si256(s3, s7, 0x31); \
} while(0)

#define BLAKE2S_COMPRESS_V8(v, m, t0, t1, f0) do {                      \
  const __m256i flag_mask = _mm256_set_epi32(-1, 0, 0, 0, 0, 0, 0, 0);  \
  __m256i iv[8], w[16];                                                 \
  int i, r;                                                             \
  for(i = 0; i < 8; ++i) {                                              \
    iv[i] = v[i];                                                       \
  }                                                                     \
  v[ 8] = _mm256_set1_epi32(blake2s_IV[0]);                             \
  v[ 9] = _mm256_set1_epi32(blake2s_IV[1]);                             \
  v[10] = _mm256_set1_epi32(blake2s_IV[2]);                             \
  v[11] = _mm256_set1_epi32(blake2s_IV[3]);                             \
  v[12] = XOR(_mm256_set1_epi32(blake2s_IV[4]), t0);                    \
  v[13] = XOR(_mm256_set1_epi32(blake2s_IV[5]), t1);                    \
  v[14] = XOR(_mm256_set1_epi32(blake2s_IV[6]), f0);                    \
  v[15] = XOR(_mm256_set1_epi32(blake2s_IV[7]), AND(f0, flag_mask));    \
  BLAKE2S_LOADMSG_V8(w, m);                                             \
  for(r = 0; r < 10; ++r) {                                             \
    BLAKE2S_ROUND_V8(v, w, r);                                          \
  }                                                                     \
  for(i = 0; i < 8; ++i) {                                              \
    v[i] = XOR(XOR(v[i], v[i+8]), iv[i]);                               \
  }                                                                     \
} while(0)


int blake2sp(uint8_t * out, const uint8_t * in, size_t inlen) {
  ALIGN(64) uint8_t buffer[8 * BLAKE2S_BLOCKBYTES];
  __m256i v[16];
  union {
    __m256i t[8];
    __m128i s[2*8];
  } lanes;
  union {
    __m256i  v;
    uint32_t w[8];
  } counterl = { 0 }, counterh = { 0 };
  int i, lane;

  for(i = 0; i < 8; ++i) {
    v[i] = _mm256_set1_epi32(blake2s_IV[i]);
  }

  v[0] = XOR(v[0], _mm256_set1_epi32(0x02080020U));
  v[2] = XOR(v[2], _mm256_set_epi32(7, 6, 5, 4, 3, 2, 1, 0));
  v[3] = XOR(v[3], _mm256_set1_epi32(0x20000000U));

  do {
    size_t block_size = 8 * BLAKE2S_BLOCKBYTES;
    const uint8_t * ptr = in;
    __m256i x0, x1, x2, x3, x4, x5, f0;

    if(inlen < block_size) {
      memcpy(buffer, in, inlen);
      memset(buffer + inlen, 0, 8 * BLAKE2S_BLOCKBYTES - inlen);
      block_size = inlen;
      ptr = buffer;
    }

    /* Some adhoc unsigned comparisons */
#define _mm256_not_si256(x) _mm256_xor_si256((x), _mm256_set1_epi32(-1))
#define _mm256_cmpge_epu32(x, y) _mm256_cmpeq_epi32((x), _mm256_max_epu32((x), (y)))
#define _mm256_cmple_epu32(x, y) _mm256_cmpge_epu32((y), (x))
#define _mm256_cmpgt_epu32(x, y) _mm256_not_si256(_mm256_cmple_epu32((x), (y)))
#define _mm256_cmplt_epu32(x, y) _mm256_cmpgt_epu32((y), (x))

    x0 = _mm256_set1_epi32(inlen & 0xFFFFFFFFUL);
    x1 = _mm256_set1_epi32(inlen / (1ULL << 32));
    /* x2 = inlen < 2^32 ? -1 : 0 */
    x2 = _mm256_cmpeq_epi32(x1, _mm256_setzero_si256());
    /* x3 = inlen > {448, ..., 0} ? -1 : 0 */
    x3 = _mm256_cmpge_epu32(x0, _mm256_set_epi32(448+1, 384+1, 320+1, 256+1, 192+1, 128+1, 64+1, 0+1));
    /* if inlen > {448, ..., 0}, inlen - {448, ..., 0} */
    /* otherwise 0 */
    x4 = _mm256_and_si256(x3, _mm256_sub_epi32(x0, _mm256_set_epi32(448, 384, 320, 256, 192, 128, 64, 0)));
    /* if inlen >= 2^32, we want 64 no matter what */
    /* if inlen  < 2^32, we want min(x3, 64) */
    x5 = _mm256_xor_si256(_mm256_and_si256(x2, _mm256_min_epu32(x4, _mm256_set1_epi32(64))),
                          _mm256_andnot_si256(x2, _mm256_set1_epi32(64)));

    /* if inlen >= 2^32, we want 0 */
    /* if inlen  < 2^32, we want the comparison */
    f0 = _mm256_cmpge_epu32(_mm256_set_epi32(512+448, 512+384, 512+320, 512+256, 512+192, 512+128, 512+64, 512+0), x0);
    f0 = _mm256_and_si256(f0, x2);

    counterl.v = _mm256_add_epi32(counterl.v, x5);
    counterh.v = _mm256_sub_epi32(counterh.v, _mm256_cmplt_epu32(counterl.v, x5)); /* ch -= cl < x5 ? -1 : 0 */
    BLAKE2S_COMPRESS_V8(v, ptr, counterl.v, counterh.v, f0);
    in    += block_size;
    inlen -= block_size;
  } while(inlen >= 8 * BLAKE2S_BLOCKBYTES);

  BLAKE2S_UNPACK_STATE_V8(lanes.t, v);

  for(lane = 0; lane < 8; ++lane) {
    size_t block_size = BLAKE2S_BLOCKBYTES;
    const uint8_t * ptr = in;
    if(!inlen) break;
    if(inlen < block_size) {
      memcpy(buffer, in, inlen);
      memset(buffer + inlen, 0, BLAKE2S_BLOCKBYTES - inlen);
      block_size = inlen;
      ptr = buffer;
    }
    counterl.w[lane] += block_size;
    counterh.w[lane] += counterl.w[lane] < block_size;
    BLAKE2S_COMPRESS_V1(lanes.s[lane*2+0], lanes.s[lane*2+1], ptr, counterl.w[lane], counterh.w[lane], -1, -(lane == 7));
    in    += block_size;
    inlen -= block_size;
  }
  return blake2s_root(out, (void *)lanes.s);
}

#if defined(SUPERCOP)
int crypto_hash(unsigned char *out, const unsigned char *in, unsigned long long inlen) {
  return blake2sp(out, in, (size_t)inlen);
}
#endif

#if defined(BLAKE2SP_SELFTEST)
#include "blake2-kat.h"
#include <stdio.h>
int main(void) {
  uint8_t buf[BLAKE2_KAT_LENGTH];
  unsigned long i;

  for( i = 0; i < BLAKE2_KAT_LENGTH; ++i ) {
    buf[i] = i;
  }

  for( i = 0; i < BLAKE2_KAT_LENGTH; ++i ) {
    uint8_t hash[BLAKE2S_OUTBYTES];
    blake2sp( hash, buf, i );

    if( 0 != memcmp( hash, blake2sp_kat[i], BLAKE2S_OUTBYTES ) ) {
      printf( "error at %lu", i );
      return -1;
    }
  }

  puts( "ok" );
  return 0;
}
#endif
