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

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <smmintrin.h>
#include <wmmintrin.h>
#include <immintrin.h>
#include <emmintrin.h>
#include "KeccakP-1600-SnP.h"

#include "brg_endian.h"
#if (PLATFORM_BYTE_ORDER != IS_LITTLE_ENDIAN)
#error Expecting a little-endian platform
#endif

#ifdef ALIGN
#undef ALIGN
#endif

#if defined(__GNUC__)
#define ALIGN(x) __attribute__ ((aligned(x)))
#elif defined(_MSC_VER)
#define ALIGN(x) __declspec(align(x))
#elif defined(__ARMCC_VERSION)
#define ALIGN(x) __align(x)
#else
#define ALIGN(x)
#endif

typedef uint8_t     UINT8;
typedef uint32_t    UINT32;
typedef uint64_t    UINT64;

typedef __m128i     V128;
typedef __m256i     V256;
typedef __m512i     V512;

#if defined(KeccakP1600times4_useAVX512)

#define XOR(a,b)                    _mm256_xor_si256(a,b)
#define XOR3(a,b,c)                 _mm256_ternarylogic_epi64(a,b,c,0x96)
#define XOR5(a,b,c,d,e)             XOR3(XOR3(a,b,c),d,e)
#define XOR512(a,b)                 _mm512_xor_si512(a,b)
#define ROL(a,offset)               _mm256_rol_epi64(a,offset)
#define Chi(a,b,c)                  _mm256_ternarylogic_epi64(a,b,c,0xD2)

#define CONST256_64(a)              (V256)_mm256_broadcast_sd((const double*)(&a))
#define LOAD4_32(a,b,c,d)           _mm_set_epi32((UINT64)(a), (UINT32)(b), (UINT32)(c), (UINT32)(d))
#define LOAD8_32(a,b,c,d,e,f,g,h)   _mm256_set_epi32((UINT64)(a), (UINT32)(b), (UINT32)(c), (UINT32)(d), (UINT32)(e), (UINT32)(f), (UINT32)(g), (UINT32)(h))
#define LOAD_GATHER4_64(idx,p)      _mm256_i32gather_epi64( (const void*)(p), idx, 8)
#define LOAD_GATHER8_64(idx,p)      _mm512_i32gather_epi64( idx, (const void*)(p), 8)
#define STORE_SCATTER4_64(p,idx, v) _mm256_i32scatter_epi64( (void*)(p), idx, v, 8)
#define STORE_SCATTER8_64(p,idx, v) _mm512_i32scatter_epi64( (void*)(p), idx, v, 8)

#endif

#define laneIndex(instanceIndex, lanePosition)  ((lanePosition)*4 + instanceIndex)
#define SnP_laneLengthInBytes                   8

void KeccakP1600times4_InitializeAll(void *states)
{
    memset(states, 0, KeccakP1600times4_statesSizeInBytes);
}

void KeccakP1600times4_AddBytes(void *states, unsigned int instanceIndex, const unsigned char *data, unsigned int offset, unsigned int length)
{
    unsigned int sizeLeft = length;
    unsigned int lanePosition = offset/SnP_laneLengthInBytes;
    unsigned int offsetInLane = offset%SnP_laneLengthInBytes;
    const unsigned char *curData = data;
    UINT64 *statesAsLanes = states;

    if ((sizeLeft > 0) && (offsetInLane != 0)) {
        unsigned int bytesInLane = SnP_laneLengthInBytes - offsetInLane;
        UINT64 lane = 0;
        if (bytesInLane > sizeLeft)
            bytesInLane = sizeLeft;
        memcpy((unsigned char*)&lane + offsetInLane, curData, bytesInLane);
        statesAsLanes[laneIndex(instanceIndex, lanePosition)] ^= lane;
        sizeLeft -= bytesInLane;
        lanePosition++;
        curData += bytesInLane;
    }

    while(sizeLeft >= SnP_laneLengthInBytes) {
        UINT64 lane = *((const UINT64*)curData);
        statesAsLanes[laneIndex(instanceIndex, lanePosition)] ^= lane;
        sizeLeft -= SnP_laneLengthInBytes;
        lanePosition++;
        curData += SnP_laneLengthInBytes;
    }

    if (sizeLeft > 0) {
        UINT64 lane = 0;
        memcpy(&lane, curData, sizeLeft);
        statesAsLanes[laneIndex(instanceIndex, lanePosition)] ^= lane;
    }
}

void KeccakP1600times4_AddLanesAll(void *states, const unsigned char *data, unsigned int laneCount, unsigned int laneOffset)
{
    V256 *stateAsLanes256 = states;
    V512 *stateAsLanes512 = states;
    const UINT64 *dataAsLanes = (const UINT64 *)data;
    unsigned int i;
    V256 index512;
    V128 index256;

    #define Add_In1( argIndex )  stateAsLanes256[argIndex] = XOR(stateAsLanes256[argIndex], LOAD_GATHER4_64(index256, dataAsLanes+argIndex))
    #define Add_In2( argIndex )  stateAsLanes512[argIndex/2] = XOR512(stateAsLanes512[argIndex/2], LOAD_GATHER8_64(index512, dataAsLanes+argIndex))
    index256 = LOAD4_32(3*laneOffset, 2*laneOffset, 1*laneOffset, 0*laneOffset);
    index512 = LOAD8_32(3*laneOffset+1, 2*laneOffset+1, 1*laneOffset+1, 0*laneOffset+1, 3*laneOffset, 2*laneOffset, 1*laneOffset, 0*laneOffset);
    if ( laneCount >= 16 )  {
        Add_In2( 0 );
        Add_In2( 2 );
        Add_In2( 4 );
        Add_In2( 6 );
        Add_In2( 8 );
        Add_In2( 10 );
        Add_In2( 12 );
        Add_In2( 14 );
        if ( laneCount >= 20 )  {
            Add_In2( 16 );
            Add_In2( 18 );
            for(i=20; i<laneCount; i++)
                Add_In1( i );
        }
        else {
            for(i=16; i<laneCount; i++)
                Add_In1( i );
        }
    }
    else {
        for(i=0; i<laneCount; i++)
            Add_In1( i );
    }
    #undef  Add_In1
    #undef  Add_In2
}

void KeccakP1600times4_ExtractBytes(const void *states, unsigned int instanceIndex, unsigned char *data, unsigned int offset, unsigned int length)
{
    unsigned int sizeLeft = length;
    unsigned int lanePosition = offset/SnP_laneLengthInBytes;
    unsigned int offsetInLane = offset%SnP_laneLengthInBytes;
    unsigned char *curData = data;
    const UINT64 *statesAsLanes = states;

    if ((sizeLeft > 0) && (offsetInLane != 0)) {
        unsigned int bytesInLane = SnP_laneLengthInBytes - offsetInLane;
        if (bytesInLane > sizeLeft)
            bytesInLane = sizeLeft;
        memcpy( curData, ((unsigned char *)&statesAsLanes[laneIndex(instanceIndex, lanePosition)]) + offsetInLane, bytesInLane);
        sizeLeft -= bytesInLane;
        lanePosition++;
        curData += bytesInLane;
    }

    while(sizeLeft >= SnP_laneLengthInBytes) {
        *(UINT64*)curData = statesAsLanes[laneIndex(instanceIndex, lanePosition)];
        sizeLeft -= SnP_laneLengthInBytes;
        lanePosition++;
        curData += SnP_laneLengthInBytes;
    }

    if (sizeLeft > 0) {
        memcpy( curData, &statesAsLanes[laneIndex(instanceIndex, lanePosition)], sizeLeft);
    }
}

void KeccakP1600times4_ExtractLanesAll(const void *states, unsigned char *data, unsigned int laneCount, unsigned int laneOffset)
{
    const V256 *stateAsLanes256 = states;
    const V512 *stateAsLanes512 = states;
    UINT64 *dataAsLanes = (UINT64 *)data;
    unsigned int i;
    V256 index512;
    V128 index256;

    #define Extr1( argIndex )  STORE_SCATTER4_64(dataAsLanes+argIndex, index256, stateAsLanes256[argIndex])
    #define Extr2( argIndex )  STORE_SCATTER8_64(dataAsLanes+argIndex, index512, stateAsLanes512[argIndex/2])
    index256 = LOAD4_32(3*laneOffset, 2*laneOffset, 1*laneOffset, 0*laneOffset);
    index512 = LOAD8_32(3*laneOffset+1, 2*laneOffset+1, 1*laneOffset+1, 0*laneOffset+1, 3*laneOffset, 2*laneOffset, 1*laneOffset, 0*laneOffset);
    if ( laneCount >= 16 )  {
        Extr2( 0 );
        Extr2( 2 );
        Extr2( 4 );
        Extr2( 6 );
        Extr2( 8 );
        Extr2( 10 );
        Extr2( 12 );
        Extr2( 14 );
        if ( laneCount >= 20 )  {
            Extr2( 16 );
            Extr2( 18 );
            for(i=20; i<laneCount; i++)
                Extr1( i );
        }
        else {
            for(i=16; i<laneCount; i++)
                Extr1( i );
        }
    }
    else {
        for(i=0; i<laneCount; i++)
            Extr1( i );
    }
    #undef  Extr1
    #undef  Extr2
}

static ALIGN(KeccakP1600times4_statesAlignment) const UINT64 KeccakP1600RoundConstants[24] = {
    0x0000000000000001ULL,
    0x0000000000008082ULL,
    0x800000000000808aULL,
    0x8000000080008000ULL,
    0x000000000000808bULL,
    0x0000000080000001ULL,
    0x8000000080008081ULL,
    0x8000000000008009ULL,
    0x000000000000008aULL,
    0x0000000000000088ULL,
    0x0000000080008009ULL,
    0x000000008000000aULL,
    0x000000008000808bULL,
    0x800000000000008bULL,
    0x8000000000008089ULL,
    0x8000000000008003ULL,
    0x8000000000008002ULL,
    0x8000000000000080ULL,
    0x000000000000800aULL,
    0x800000008000000aULL,
    0x8000000080008081ULL,
    0x8000000000008080ULL,
    0x0000000080000001ULL,
    0x8000000080008008ULL};

#define KeccakP_DeclareVars \
    V256    _Ba, _Be, _Bi, _Bo, _Bu; \
    V256    _Da, _De, _Di, _Do, _Du; \
    V256    _ba, _be, _bi, _bo, _bu; \
    V256    _ga, _ge, _gi, _go, _gu; \
    V256    _ka, _ke, _ki, _ko, _ku; \
    V256    _ma, _me, _mi, _mo, _mu; \
    V256    _sa, _se, _si, _so, _su

#define KeccakP_ThetaRhoPiChi( _L1, _L2, _L3, _L4, _L5, _Bb1, _Bb2, _Bb3, _Bb4, _Bb5, _Rr1, _Rr2, _Rr3, _Rr4, _Rr5 ) \
    _Bb1 = XOR(_L1, _Da); \
    _Bb2 = XOR(_L2, _De); \
    _Bb3 = XOR(_L3, _Di); \
    _Bb4 = XOR(_L4, _Do); \
    _Bb5 = XOR(_L5, _Du); \
    if (_Rr1 != 0) _Bb1 = ROL(_Bb1, _Rr1); \
    _Bb2 = ROL(_Bb2, _Rr2); \
    _Bb3 = ROL(_Bb3, _Rr3); \
    _Bb4 = ROL(_Bb4, _Rr4); \
    _Bb5 = ROL(_Bb5, _Rr5); \
    _L1 = Chi( _Ba, _Be, _Bi); \
    _L2 = Chi( _Be, _Bi, _Bo); \
    _L3 = Chi( _Bi, _Bo, _Bu); \
    _L4 = Chi( _Bo, _Bu, _Ba); \
    _L5 = Chi( _Bu, _Ba, _Be);

#define KeccakP_ThetaRhoPiChiIota0( _L1, _L2, _L3, _L4, _L5, _rc ) \
    _Ba = XOR5( _ba, _ga, _ka, _ma, _sa ); /* Theta effect */ \
    _Be = XOR5( _be, _ge, _ke, _me, _se ); \
    _Bi = XOR5( _bi, _gi, _ki, _mi, _si ); \
    _Bo = XOR5( _bo, _go, _ko, _mo, _so ); \
    _Bu = XOR5( _bu, _gu, _ku, _mu, _su ); \
    _Da = ROL( _Be, 1 ); \
    _De = ROL( _Bi, 1 ); \
    _Di = ROL( _Bo, 1 ); \
    _Do = ROL( _Bu, 1 ); \
    _Du = ROL( _Ba, 1 ); \
    _Da = XOR( _Da, _Bu ); \
    _De = XOR( _De, _Ba ); \
    _Di = XOR( _Di, _Be ); \
    _Do = XOR( _Do, _Bi ); \
    _Du = XOR( _Du, _Bo ); \
    KeccakP_ThetaRhoPiChi( _L1, _L2, _L3, _L4, _L5, _Ba, _Be, _Bi, _Bo, _Bu,  0, 44, 43, 21, 14 ); \
    _L1 = XOR(_L1, _rc) /* Iota */

#define KeccakP_ThetaRhoPiChi1( _L1, _L2, _L3, _L4, _L5 ) \
    KeccakP_ThetaRhoPiChi( _L1, _L2, _L3, _L4, _L5, _Bi, _Bo, _Bu, _Ba, _Be,  3, 45, 61, 28, 20 )

#define KeccakP_ThetaRhoPiChi2( _L1, _L2, _L3, _L4, _L5 ) \
    KeccakP_ThetaRhoPiChi( _L1, _L2, _L3, _L4, _L5, _Bu, _Ba, _Be, _Bi, _Bo, 18,  1,  6, 25,  8 )

#define KeccakP_ThetaRhoPiChi3( _L1, _L2, _L3, _L4, _L5 ) \
    KeccakP_ThetaRhoPiChi( _L1, _L2, _L3, _L4, _L5, _Be, _Bi, _Bo, _Bu, _Ba, 36, 10, 15, 56, 27 )

#define KeccakP_ThetaRhoPiChi4( _L1, _L2, _L3, _L4, _L5 ) \
    KeccakP_ThetaRhoPiChi( _L1, _L2, _L3, _L4, _L5, _Bo, _Bu, _Ba, _Be, _Bi, 41,  2, 62, 55, 39 )

#define KeccakP_4rounds( i ) \
    KeccakP_ThetaRhoPiChiIota0(_ba, _ge, _ki, _mo, _su, CONST256_64(KeccakP1600RoundConstants[i]) ); \
    KeccakP_ThetaRhoPiChi1(    _ka, _me, _si, _bo, _gu ); \
    KeccakP_ThetaRhoPiChi2(    _sa, _be, _gi, _ko, _mu ); \
    KeccakP_ThetaRhoPiChi3(    _ga, _ke, _mi, _so, _bu ); \
    KeccakP_ThetaRhoPiChi4(    _ma, _se, _bi, _go, _ku ); \
\
    KeccakP_ThetaRhoPiChiIota0(_ba, _me, _gi, _so, _ku, CONST256_64(KeccakP1600RoundConstants[i+1]) ); \
    KeccakP_ThetaRhoPiChi1(    _sa, _ke, _bi, _mo, _gu ); \
    KeccakP_ThetaRhoPiChi2(    _ma, _ge, _si, _ko, _bu ); \
    KeccakP_ThetaRhoPiChi3(    _ka, _be, _mi, _go, _su ); \
    KeccakP_ThetaRhoPiChi4(    _ga, _se, _ki, _bo, _mu ); \
\
    KeccakP_ThetaRhoPiChiIota0(_ba, _ke, _si, _go, _mu, CONST256_64(KeccakP1600RoundConstants[i+2]) ); \
    KeccakP_ThetaRhoPiChi1(    _ma, _be, _ki, _so, _gu ); \
    KeccakP_ThetaRhoPiChi2(    _ga, _me, _bi, _ko, _su ); \
    KeccakP_ThetaRhoPiChi3(    _sa, _ge, _mi, _bo, _ku ); \
    KeccakP_ThetaRhoPiChi4(    _ka, _se, _gi, _mo, _bu ); \
\
    KeccakP_ThetaRhoPiChiIota0(_ba, _be, _bi, _bo, _bu, CONST256_64(KeccakP1600RoundConstants[i+3]) ); \
    KeccakP_ThetaRhoPiChi1(    _ga, _ge, _gi, _go, _gu ); \
    KeccakP_ThetaRhoPiChi2(    _ka, _ke, _ki, _ko, _ku ); \
    KeccakP_ThetaRhoPiChi3(    _ma, _me, _mi, _mo, _mu ); \
    KeccakP_ThetaRhoPiChi4(    _sa, _se, _si, _so, _su )

#ifdef KeccakP1600times4_fullUnrolling

#define rounds12 \
    KeccakP_4rounds( 12 ); \
    KeccakP_4rounds( 16 ); \
    KeccakP_4rounds( 20 )

#elif (KeccakP1600times4_unrolling == 4)

#define rounds12 \
    i = 12; \
    do { \
        KeccakP_4rounds( i ); \
    } while( (i += 4) < 24 )

#elif (KeccakP1600times4_unrolling == 12)

#define rounds12 \
    KeccakP_4rounds( 12 ); \
    KeccakP_4rounds( 16 ); \
    KeccakP_4rounds( 20 )

#else
#error "Unrolling is not correctly specified!"
#endif

#define copyFromState(pState) \
    _ba = pState[ 0]; \
    _be = pState[ 1]; \
    _bi = pState[ 2]; \
    _bo = pState[ 3]; \
    _bu = pState[ 4]; \
    _ga = pState[ 5]; \
    _ge = pState[ 6]; \
    _gi = pState[ 7]; \
    _go = pState[ 8]; \
    _gu = pState[ 9]; \
    _ka = pState[10]; \
    _ke = pState[11]; \
    _ki = pState[12]; \
    _ko = pState[13]; \
    _ku = pState[14]; \
    _ma = pState[15]; \
    _me = pState[16]; \
    _mi = pState[17]; \
    _mo = pState[18]; \
    _mu = pState[19]; \
    _sa = pState[20]; \
    _se = pState[21]; \
    _si = pState[22]; \
    _so = pState[23]; \
    _su = pState[24]

#define copyToState(pState) \
    pState[ 0] = _ba; \
    pState[ 1] = _be; \
    pState[ 2] = _bi; \
    pState[ 3] = _bo; \
    pState[ 4] = _bu; \
    pState[ 5] = _ga; \
    pState[ 6] = _ge; \
    pState[ 7] = _gi; \
    pState[ 8] = _go; \
    pState[ 9] = _gu; \
    pState[10] = _ka; \
    pState[11] = _ke; \
    pState[12] = _ki; \
    pState[13] = _ko; \
    pState[14] = _ku; \
    pState[15] = _ma; \
    pState[16] = _me; \
    pState[17] = _mi; \
    pState[18] = _mo; \
    pState[19] = _mu; \
    pState[20] = _sa; \
    pState[21] = _se; \
    pState[22] = _si; \
    pState[23] = _so; \
    pState[24] = _su

void KeccakP1600times4_PermuteAll_12rounds(void *states)
{
    V256 *statesAsLanes = states;
    KeccakP_DeclareVars;
    #if (KeccakP1600times4_unrolling < 12)
    unsigned int i;
    #endif

    copyFromState(statesAsLanes);
    rounds12;
    copyToState(statesAsLanes);
}

size_t KeccakP1600times4_12rounds_FastLoop_Absorb(void *states, unsigned int laneCount, unsigned int laneOffsetParallel, unsigned int laneOffsetSerial, const unsigned char *data, size_t dataByteLen)
{
    size_t dataMinimumSize = (laneOffsetParallel*3 + laneCount)*8;

    if (laneCount == 21) {
        #if (KeccakP1600times4_unrolling < 12)
        unsigned int i;
        #endif
        const unsigned char *dataStart = data;
        V256 *statesAsLanes = states;
        const UINT64 *dataAsLanes = (const UINT64 *)data;
        KeccakP_DeclareVars;
        V128 index;

        copyFromState(statesAsLanes);
        index = LOAD4_32(3*laneOffsetParallel, 2*laneOffsetParallel, 1*laneOffsetParallel, 0*laneOffsetParallel);
        while(dataByteLen >= dataMinimumSize) {
            #define Add_In( argLane, argIndex )  argLane = XOR(argLane, LOAD_GATHER4_64(index, dataAsLanes+argIndex))
            Add_In( _ba, 0 );
            Add_In( _be, 1 );
            Add_In( _bi, 2 );
            Add_In( _bo, 3 );
            Add_In( _bu, 4 );
            Add_In( _ga, 5 );
            Add_In( _ge, 6 );
            Add_In( _gi, 7 );
            Add_In( _go, 8 );
            Add_In( _gu, 9 );
            Add_In( _ka, 10 );
            Add_In( _ke, 11 );
            Add_In( _ki, 12 );
            Add_In( _ko, 13 );
            Add_In( _ku, 14 );
            Add_In( _ma, 15 );
            Add_In( _me, 16 );
            Add_In( _mi, 17 );
            Add_In( _mo, 18 );
            Add_In( _mu, 19 );
            Add_In( _sa, 20 );
            #undef  Add_In
            rounds12;
            dataAsLanes += laneOffsetSerial;
            dataByteLen -= laneOffsetSerial*8;
        }
        copyToState(statesAsLanes);
        return (const unsigned char *)dataAsLanes - dataStart;
    }
    else {
        const unsigned char *dataStart = data;

        while(dataByteLen >= dataMinimumSize) {
            KeccakP1600times4_AddLanesAll(states, data, laneCount, laneOffsetParallel);
            KeccakP1600times4_PermuteAll_12rounds(states);
            data += laneOffsetSerial*8;
            dataByteLen -= laneOffsetSerial*8;
        }
        return data - dataStart;
    }
}
