/*
Implementation by Ronny Van Keer, hereby denoted as "the implementer".

For more information, feedback or questions, please refer to our website:
https://keccak.team/

To the extent possible under law, the implementer has waived all copyright
and related or neighboring rights to the source code in this file.
http://creativecommons.org/publicdomain/zero/1.0/

---

Please refer to the XKCP for more details.
*/

#ifndef _KeccakP_1600_SnP_h_
#define _KeccakP_1600_SnP_h_

#include <stddef.h>
#include "KeccakP-1600-config.h"

#define KeccakP1600_implementation      "AVX2 optimized implementation"
#define KeccakP1600_stateSizeInBytes    200
#define KeccakP1600_stateAlignment      32
#define KeccakP1600_12rounds_FastLoop_supported

#define KeccakP1600_StaticInitialize()
void KeccakP1600_Initialize(void *state);
void KeccakP1600_AddByte(void *state, unsigned char data, unsigned int offset);
void KeccakP1600_AddBytes(void *state, const unsigned char *data, unsigned int offset, unsigned int length);
void KeccakP1600_Permute_12rounds(void *state);
void KeccakP1600_ExtractBytes(const void *state, unsigned char *data, unsigned int offset, unsigned int length);
size_t KeccakP1600_12rounds_FastLoop_Absorb(void *state, unsigned int laneCount, const unsigned char *data, size_t dataByteLen);

#define KeccakP1600times2_implementation        "128-bit SIMD implementation (" KeccakP1600times2_implementation_config ")"
#define KeccakP1600times2_statesSizeInBytes     400
#define KeccakP1600times2_statesAlignment       16

#define KeccakP1600times2_StaticInitialize()
void KeccakP1600times2_InitializeAll(void *states);
#define KeccakP1600times2_AddByte(states, instanceIndex, byte, offset) \
    ((unsigned char*)(states))[(instanceIndex)*8 + ((offset)/8)*2*8 + (offset)%8] ^= (byte)
void KeccakP1600times2_AddBytes(void *states, unsigned int instanceIndex, const unsigned char *data, unsigned int offset, unsigned int length);
void KeccakP1600times2_AddLanesAll(void *states, const unsigned char *data, unsigned int laneCount, unsigned int laneOffset);
void KeccakP1600times2_PermuteAll_12rounds(void *states);
void KeccakP1600times2_ExtractBytes(const void *states, unsigned int instanceIndex, unsigned char *data, unsigned int offset, unsigned int length);
void KeccakP1600times2_ExtractLanesAll(const void *states, unsigned char *data, unsigned int laneCount, unsigned int laneOffset);

#define KeccakP1600times4_implementation        "256-bit SIMD implementation (" KeccakP1600times4_implementation_config ")"
#define KeccakP1600times4_statesSizeInBytes     800
#define KeccakP1600times4_statesAlignment       32
#define KeccakP1600times4_12rounds_FastLoop_supported

#define KeccakP1600times4_StaticInitialize()
void KeccakP1600times4_InitializeAll(void *states);
#define KeccakP1600times4_AddByte(states, instanceIndex, byte, offset) \
    ((unsigned char*)(states))[(instanceIndex)*8 + ((offset)/8)*4*8 + (offset)%8] ^= (byte)
void KeccakP1600times4_AddBytes(void *states, unsigned int instanceIndex, const unsigned char *data, unsigned int offset, unsigned int length);
void KeccakP1600times4_AddLanesAll(void *states, const unsigned char *data, unsigned int laneCount, unsigned int laneOffset);
void KeccakP1600times4_PermuteAll_12rounds(void *states);
void KeccakP1600times4_ExtractBytes(const void *states, unsigned int instanceIndex, unsigned char *data, unsigned int offset, unsigned int length);
void KeccakP1600times4_ExtractLanesAll(const void *states, unsigned char *data, unsigned int laneCount, unsigned int laneOffset);
size_t KeccakP1600times4_12rounds_FastLoop_Absorb(void *states, unsigned int laneCount, unsigned int laneOffsetParallel, unsigned int laneOffsetSerial, const unsigned char *data, size_t dataByteLen);

#endif
