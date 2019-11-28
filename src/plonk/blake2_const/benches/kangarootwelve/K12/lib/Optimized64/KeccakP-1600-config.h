#define KeccakP1600_implementation_config "all rounds unrolled"
#define KeccakP1600_fullUnrolling

/* Or */
/*
#define KeccakP1600_implementation_config "6 rounds unrolled"
#define KeccakP1600_unrolling 6
*/

/* Or */
/*
#define KeccakP1600_implementation_config "lane complementing, 6 rounds unrolled"
#define KeccakP1600_unrolling 6
#define KeccakP1600_useLaneComplementing
*/

/* Or */
/*
#define KeccakP1600_implementation_config "lane complementing, all rounds unrolled"
#define KeccakP1600_fullUnrolling
#define KeccakP1600_useLaneComplementing
*/

/* Or */
/*
#define KeccakP1600_implementation_config "lane complementing, all rounds unrolled, using SHLD for rotations"
#define KeccakP1600_fullUnrolling
#define KeccakP1600_useLaneComplementing
#define KeccakP1600_useSHLD
*/
