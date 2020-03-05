#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if defined(_MSC_VER)
#include <intrin.h>
#endif

extern int crypto_hash(unsigned char *out, const unsigned char *in, unsigned long long inlen);

static int bench_cmp( const void *x, const void *y ) {
  const int64_t *ix = (const int64_t *)x;
  const int64_t *iy = (const int64_t *)y;
  return *ix - *iy;
}

#if defined(_MSC_VER)
static uint64_t cpucycles(void) {
  return __rdtsc();
}
#else
#if   defined(__i386__)
static uint64_t cpucycles(void) {
  uint64_t result;
  __asm__ __volatile__(
    "rdtsc\n"
    : "=A" ( result )
  );
  return result;
}
#elif defined(__x86_64__)
static uint64_t cpucycles(void) {
  uint64_t result;
  __asm__ __volatile__(
    "rdtsc\n"
    "shlq $32,%%rdx\n"
    "orq %%rdx,%%rax"
    : "=a" ( result ) ::  "%rdx"
  );
  return result;
}
#else
#error "Don't know how to count cycles!"
#endif
#endif /* _MSC_VER */

#define BENCH_TRIALS    512
#define BENCH_MAXLEN   1536

int main(void) {
  static  uint8_t in[4096];
  static uint64_t median[4096 + 1];
  int i, j;

  printf( "#bytes  median  per byte\n" );
  /* 1 ... BENCH_MAXLEN */
  for(j = 0; j <= 4096; ++j) {
    uint64_t cycles[BENCH_TRIALS + 1];

    for(i = 0; i <= BENCH_TRIALS; ++i) {
      cycles[i] = cpucycles();
      crypto_hash(in, in, j);
    }

    for(i = 0; i < BENCH_TRIALS; ++i) {
      cycles[i] = cycles[i + 1] - cycles[i];
    }

    qsort(cycles, BENCH_TRIALS, sizeof(uint64_t), bench_cmp);
    median[j] = cycles[BENCH_TRIALS / 2];
  }

  for( j = 0; j <= BENCH_MAXLEN; j += 8 ) {
    printf("%5d   %7.2f\n", j, (double)median[j] / j);
  }

  printf( "#2048   %7.2f\n", (double)median[2048] / 2048.0 );
  printf( "#4096   %7.2f\n", (double)median[4096] / 4096.0 );
  printf( "#long   %7.2f\n", (double)(median[4096] - median[2048]) / 2048.0);
  return 0;
}
