/*
Implementation by Ronny Van Keer, hereby denoted as "the implementer".

For more information, feedback or questions, please refer to our website:
https://keccak.team/

To the extent possible under law, the implementer has waived all copyright
and related or neighboring rights to the source code in this file.
http://creativecommons.org/publicdomain/zero/1.0/
*/

#include "KangarooTwelve.h"

/* #define OUTPUT */
/* #define VERBOSE */

#define SnP_width               1600
#define inputByteSize           (80*1024)
#define outputByteSize          256
#define customizationByteSize   32
#define checksumByteSize        16
#define cChunkSize              8192

#if (defined(OUTPUT) || defined(VERBOSE) || !defined(EMBEDDED))
#include <stdio.h>
#endif
#include <stdlib.h>
#include <string.h>

#if defined(EMBEDDED)
static void assert(int condition)
{
    if (!condition)
    {
        for ( ; ; ) ;
    }
}
#else
#include <assert.h>
#endif

static void generateSimpleRawMaterial(unsigned char* data, unsigned int length, unsigned char seed1, unsigned int seed2)
{
    unsigned int i;

    for(i=0; i<length; i++) {
        unsigned char iRolled;
        unsigned char byte;
        seed2 = seed2 % 8;
        iRolled = ((unsigned char)i << seed2) | ((unsigned char)i >> (8-seed2));
        byte = seed1 + 161*length - iRolled + i;
        data[i] = byte;
    }
}

static void performTestKangarooTwelveOneInput(unsigned int inputLen, unsigned int outputLen, unsigned int customLen, KangarooTwelve_Instance *pSpongeChecksum, unsigned int mode, unsigned int useSqueeze)
{
    unsigned char input[inputByteSize];
    unsigned char output[outputByteSize];
    unsigned char customization[customizationByteSize];
    int result;
    unsigned int i;

    generateSimpleRawMaterial(customization, customizationByteSize, customLen, 97);
    generateSimpleRawMaterial(input, inputLen, outputLen, inputLen + customLen);

    #ifdef VERBOSE
    printf( "outputLen %5u, inputLen %5u, customLen %3u\n", outputLen, inputLen, customLen);
    #endif
    if (!useSqueeze)
    {
        if (mode == 0)
        {
            /* Input/Output full size in one call */
            result = KangarooTwelve( input, inputLen, output, outputLen, customization, customLen );
            assert(result == 0);
        }
        else if (mode == 1)
        {
            /* Input/Output one byte per call */
            KangarooTwelve_Instance kt;
            result = KangarooTwelve_Initialize(&kt, outputLen);
            assert(result == 0);
            for (i = 0; i < inputLen; ++i )
            {
                result = KangarooTwelve_Update(&kt, input + i, 1);
                assert(result == 0);
            }
            result =  KangarooTwelve_Final(&kt, output, customization, customLen );
            assert(result == 0);
        }
        else if (mode == 2)
        {
            /* Input/Output random number of bytes per call */
            KangarooTwelve_Instance kt;
            unsigned char *pInput = input;
            result = KangarooTwelve_Initialize(&kt, outputLen);
            assert(result == 0);
            while (inputLen)
            {
                unsigned int len = ((rand() << 15) ^ rand()) % (inputLen + 1);
                result = KangarooTwelve_Update(&kt, pInput, len);
                assert(result == 0);
                pInput += len;
                inputLen -= len;
            }
            result =  KangarooTwelve_Final(&kt, output, customization, customLen);
            assert(result == 0);
        }
    }
    else
    {
        if (mode == 0)
        {
            KangarooTwelve_Instance kt;
            result = KangarooTwelve_Initialize(&kt, 0);
            assert(result == 0);
            result = KangarooTwelve_Update(&kt, input, inputLen);
            assert(result == 0);
            result = KangarooTwelve_Final(&kt, 0, customization, customLen);
            assert(result == 0);
            result = KangarooTwelve_Squeeze(&kt, output, outputLen);
            assert(result == 0);
        }
        else if (mode == 1)
        {
            KangarooTwelve_Instance kt;
            result = KangarooTwelve_Initialize(&kt, 0);
            assert(result == 0);
            result = KangarooTwelve_Update(&kt, input, inputLen);
            assert(result == 0);
            result = KangarooTwelve_Final(&kt, 0, customization, customLen);
            assert(result == 0);

            for (i = 0; i < outputLen; ++i)
            {
                result =  KangarooTwelve_Squeeze(&kt, output + i, 1);
                assert(result == 0);
            }
        }
        else if (mode == 2)
        {
            KangarooTwelve_Instance kt;
            unsigned int len;
            result = KangarooTwelve_Initialize(&kt, 0);
            assert(result == 0);
            result = KangarooTwelve_Update(&kt, input, inputLen);
            assert(result == 0);
            result = KangarooTwelve_Final(&kt, 0, customization, customLen);
            assert(result == 0);

            for (i = 0; i < outputLen; i += len)
            {
                len = ((rand() << 15) ^ rand()) % ((outputLen-i) + 1);
                result = KangarooTwelve_Squeeze(&kt, output+i, len);
                assert(result == 0);
            }
        }
    }

    #ifdef VERBOSE
    {
        unsigned int i;

        printf("KangarooTwelve\n");
        printf("Input of %d bytes:", inputLen);
        for(i=0; (i<inputLen) && (i<16); i++)
            printf(" %02x", (int)input[i]);
        if (inputLen > 16)
            printf(" ...");
        printf("\n");
        printf("Output of %d bytes:", outputLen);
        for(i=0; i<outputLen; i++)
            printf(" %02x", (int)output[i]);
        printf("\n\n");
        fflush(stdout);
    }
    #endif

    KangarooTwelve_Update(pSpongeChecksum, output, outputLen);
}

static void performTestKangarooTwelve(unsigned char *checksum, unsigned int mode, unsigned int useSqueeze)
{
    unsigned int inputLen, outputLen, customLen;

    /* Acumulated test vector */
    KangarooTwelve_Instance spongeChecksum;
    KangarooTwelve_Initialize(&spongeChecksum, 0);

    outputLen = 256/8;
    customLen = 0;
    for(inputLen=0; inputLen<=cChunkSize*9+123; inputLen++) {
        assert(inputLen <= inputByteSize);
        performTestKangarooTwelveOneInput(inputLen, outputLen, customLen, &spongeChecksum, mode, useSqueeze);
    }
    
    for(outputLen = 128/8; outputLen <= 512/8; outputLen <<= 1)
    for(inputLen = 0; inputLen <= (3*cChunkSize) && inputLen <= inputByteSize; inputLen = inputLen ? (inputLen + 167) : 1)
    for(customLen = 0; customLen <= customizationByteSize; customLen += 7) 
    {
        assert(inputLen <= inputByteSize);
        performTestKangarooTwelveOneInput(inputLen, outputLen, customLen, &spongeChecksum, 0, useSqueeze);
    }
    KangarooTwelve_Final(&spongeChecksum, 0, (const unsigned char *)"", 0);
    KangarooTwelve_Squeeze(&spongeChecksum, checksum, checksumByteSize);

    #ifdef VERBOSE
    {
        unsigned int i;
        printf("KangarooTwelve\n" );
        printf("Checksum: ");
        for(i=0; i<checksumByteSize; i++)
            printf("\\x%02x", (int)checksum[i]);
        printf("\n\n");
    }
    #endif
}

void selfTestKangarooTwelve(const unsigned char *expected)
{
    unsigned char checksum[checksumByteSize];
    unsigned int mode, useSqueeze;

    for(useSqueeze = 0; useSqueeze <= 1; ++useSqueeze)
    for(mode = 0; mode <= 2; ++mode) {
        #ifndef EMBEDDED
        printf("Testing KangarooTwelve %u %u...", useSqueeze, mode);
        fflush(stdout);
        #endif
        performTestKangarooTwelve(checksum, mode, useSqueeze);
        assert(memcmp(expected, checksum, checksumByteSize) == 0);
        #ifndef EMBEDDED
        printf(" - OK.\n");
        #endif
    }
}

#ifdef OUTPUT
void writeTestKangarooTwelveOne(FILE *f)
{
    unsigned char checksum[checksumByteSize];
    unsigned int offset;

    performTestKangarooTwelve(checksum, 0, 0);
    fprintf(f, "    selfTestKangarooTwelve(\"");
    for(offset=0; offset<checksumByteSize; offset++)
        fprintf(f, "\\x%02x", checksum[offset]);
    fprintf(f, "\");\n");
}

void writeTestKangarooTwelve(const char *filename)
{
    FILE *f = fopen(filename, "w");
    assert(f != NULL);
    writeTestKangarooTwelveOne(f);
    fclose(f);
}
#endif

static void outputHex(const unsigned char *data, unsigned char length)
{
    #ifndef EMBEDDED
    unsigned int i;
    for(i=0; i<length; i++)
        printf("%02x ", (int)data[i]);
    printf("\n\n");
    #endif
}

void printKangarooTwelveTestVectors()
{
    unsigned char *M, *C;
    unsigned char output[10032];
    unsigned int i, j, l;

    printf("KangarooTwelve(M=empty, C=empty, 32 output bytes):\n");
    KangarooTwelve(0, 0, output, 32, 0, 0);
    outputHex(output, 32);
    printf("KangarooTwelve(M=empty, C=empty, 64 output bytes):\n");
    KangarooTwelve(0, 0, output, 64, 0, 0);
    outputHex(output, 64);
    printf("KangarooTwelve(M=empty, C=empty, 10032 output bytes), last 32 bytes:\n");
    KangarooTwelve(0, 0, output, 10032, 0, 0);
    outputHex(output+10000, 32);
    for(l=1, i=0; i<7; i++, l=l*17) {
        M = malloc(l);
        for(j=0; j<l; j++)
            M[j] = j%251;
        printf("KangarooTwelve(M=pattern 0x00 to 0xFA for 17^%d bytes, C=empty, 32 output bytes):\n", i);
        KangarooTwelve(M, l, output, 32, 0, 0);
        outputHex(output, 32);
        free(M);
    }
    for(l=1, i=0; i<4; i++, l=l*41) {
        unsigned int ll = (1 << i)-1;
        M = malloc(ll);
        memset(M, 0xFF, ll);
        C = malloc(l);
        for(j=0; j<l; j++)
            C[j] = j%251;
        printf("KangarooTwelve(M=%d times byte 0xFF, C=pattern 0x00 to 0xFA for 41^%d bytes, 32 output bytes):\n", ll, i);
        KangarooTwelve(M, ll, output, 32, C, l);
        outputHex(output, 32);
        free(M);
        free(C);
    }
}

void testKangarooTwelve(void)
{
#ifdef OUTPUT
    printKangarooTwelveTestVectors();
    writeTestKangarooTwelve("KangarooTwelve.txt");
#endif

    selfTestKangarooTwelve((const unsigned char *)"\x61\x4d\x7a\xf8\xd5\xcc\xd0\xe1\x02\x53\x7d\x21\x5e\x39\x05\xed");
}
