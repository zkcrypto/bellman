/*
Implementation by the Keccak Team, namely, Guido Bertoni, Joan Daemen,
Michaël Peeters, Gilles Van Assche and Ronny Van Keer,
hereby denoted as "the implementer".

For more information, feedback or questions, please refer to our website:
https://keccak.team/

To the extent possible under law, the implementer has waived all copyright
and related or neighboring rights to the source code in this file.
http://creativecommons.org/publicdomain/zero/1.0/
*/

#include <assert.h>
#include <math.h>
#include <stdio.h>
#include <string.h>
#include "KangarooTwelve.h"
#include "timing.h"
#include "testPerformance.h"

void displayMeasurements1101001000(uint_32t *measurements, uint_32t *laneCounts, unsigned int numberOfColumns, unsigned int laneLengthInBytes);

#define xstr(s) str(s)
#define str(s) #s

uint_32t measureKangarooTwelve(uint_32t dtMin, unsigned int inputLen)
{
    ALIGN(32) unsigned char input[1024*1024];
    ALIGN(32) unsigned char output[32];
    measureTimingDeclare

    assert(inputLen <= 1024*1024);

    memset(input, 0xA5, 16);

    measureTimingBeginDeclared
    KangarooTwelve(input, inputLen, output, 32, (const unsigned char *)"", 0);
    measureTimingEnd
}

void printKangarooTwelvePerformanceHeader( void )
{
    printf("*** KangarooTwelve ***\n");
    printf("Using Keccak-p[1600,12] implementations:\n");
    printf("- \303\2271: " KeccakP1600_implementation "\n");
    #if defined(KeccakP1600_12rounds_FastLoop_supported)
    printf("      + KeccakP1600_12rounds_FastLoop_Absorb()\n");
    #endif

    #if defined(KeccakP1600times2_implementation) && !defined(KeccakP1600times2_isFallback)
    printf("- \303\2272: " KeccakP1600times2_implementation "\n");
    #if defined(KeccakP1600times2_12rounds_FastLoop_supported)
    printf("      + KeccakP1600times2_12rounds_FastLoop_Absorb()\n");
    #endif
    #else
    printf("- \303\2272: not used\n");
    #endif

    #if defined(KeccakP1600times4_implementation) && !defined(KeccakP1600times4_isFallback)
    printf("- \303\2274: " KeccakP1600times4_implementation "\n");
    #if defined(KeccakP1600times4_12rounds_FastLoop_supported)
    printf("      + KeccakP1600times4_12rounds_FastLoop_Absorb()\n");
    #endif
    #else
    printf("- \303\2274: not used\n");
    #endif

    #if defined(KeccakP1600times8_implementation) && !defined(KeccakP1600times8_isFallback)
    printf("- \303\2278: " KeccakP1600times8_implementation "\n");
    #if defined(KeccakP1600times8_12rounds_FastLoop_supported)
    printf("      + KeccakP1600times8_12rounds_FastLoop_Absorb()\n");
    #endif
    #else
    printf("- \303\2278: not used\n");
    #endif

    printf("\n");
}

void testKangarooTwelvePerformanceOne( void )
{
    const unsigned int chunkSize = 8192;
    unsigned halfTones;
    uint_32t calibration = calibrate();
    unsigned int chunkSizeLog = (unsigned int)floor(log(chunkSize)/log(2.0)+0.5);
    int displaySlope = 0;

    measureKangarooTwelve(calibration, 500000);
    for(halfTones=chunkSizeLog*12-28; halfTones<=13*12; halfTones+=4) {
        double I = pow(2.0, halfTones/12.0);
        unsigned int i  = (unsigned int)floor(I+0.5);
        uint_32t time, timePlus1Block, timePlus2Blocks, timePlus4Blocks, timePlus8Blocks;
        uint_32t timePlus84Blocks;
        time = measureKangarooTwelve(calibration, i);
        if (i == chunkSize) {
            displaySlope = 1;
            timePlus1Block  = measureKangarooTwelve(calibration, i+1*chunkSize);
            timePlus2Blocks = measureKangarooTwelve(calibration, i+2*chunkSize);
            timePlus4Blocks = measureKangarooTwelve(calibration, i+4*chunkSize);
            timePlus8Blocks = measureKangarooTwelve(calibration, i+8*chunkSize);
            timePlus84Blocks = measureKangarooTwelve(calibration, i+84*chunkSize);
        }
        printf("%8d bytes: %9d cycles, %6.3f cycles/byte\n", i, time, time*1.0/i);
        if (displaySlope) {
            printf("     +1 block:  %9d cycles, %6.3f cycles/byte (slope)\n", timePlus1Block, (timePlus1Block-(double)(time))*1.0/chunkSize/1.0);
            printf("     +2 blocks: %9d cycles, %6.3f cycles/byte (slope)\n", timePlus2Blocks, (timePlus2Blocks-(double)(time))*1.0/chunkSize/2.0);
            printf("     +4 blocks: %9d cycles, %6.3f cycles/byte (slope)\n", timePlus4Blocks, (timePlus4Blocks-(double)(time))*1.0/chunkSize/4.0);
            printf("     +8 blocks: %9d cycles, %6.3f cycles/byte (slope)\n", timePlus8Blocks, (timePlus8Blocks-(double)(time))*1.0/chunkSize/8.0);
            printf("    +84 blocks: %9d cycles, %6.3f cycles/byte (slope)\n", timePlus84Blocks, (timePlus84Blocks-(double)(time))*1.0/chunkSize/84.0);
            displaySlope = 0;
        }
    }
    for(halfTones=12*12; halfTones<=19*12; halfTones+=4) {
        double I = chunkSize + pow(2.0, halfTones/12.0);
        unsigned int i  = (unsigned int)floor(I+0.5);
        uint_32t time;
        time = measureKangarooTwelve(calibration, i);
        printf("%8d bytes: %9d cycles, %6.3f cycles/byte\n", i, time, time*1.0/i);
    }
    printf("\n\n");
}

void testKangarooTwelvePerformance()
{
    printKangarooTwelvePerformanceHeader();
    testKangarooTwelvePerformanceOne();
}
void testPerformance()
{
    testKangarooTwelvePerformance();
}

void bubbleSort(double *list, unsigned int size)
{
    unsigned int n = size;

    do {
       unsigned int newn = 0;
       unsigned int i;

       for(i=1; i<n; i++) {
          if (list[i-1] > list[i]) {
              double temp = list[i-1];
              list[i-1] = list[i];
              list[i] = temp;
              newn = i;
          }
       }
       n = newn;
    }
    while(n > 0);
}

double med4(double x0, double x1, double x2, double x3)
{
    double list[4];
    list[0] = x0;
    list[1] = x1;
    list[2] = x2;
    list[3] = x3;
    bubbleSort(list, 4);
    if (fabs(list[2]-list[0]) < fabs(list[3]-list[1]))
        return 0.25*list[0]+0.375*list[1]+0.25*list[2]+0.125*list[3];
    else
        return 0.125*list[0]+0.25*list[1]+0.375*list[2]+0.25*list[3];
}

void displayMeasurements1101001000(uint_32t *measurements, uint_32t *laneCounts, unsigned int numberOfColumns, unsigned int laneLengthInBytes)
{
    double cpb[4];
    unsigned int i;

    for(i=0; i<numberOfColumns; i++) {
        uint_32t bytes = laneCounts[i]*laneLengthInBytes;
        double x = med4(measurements[i*4+0]*1.0, measurements[i*4+1]/10.0, measurements[i*4+2]/100.0, measurements[i*4+3]/1000.0);
        cpb[i] = x/bytes;
    }
    if (numberOfColumns == 1) {
        printf("     laneCount:  %5d\n", laneCounts[0]);
        printf("       1 block:  %5d\n", measurements[0]);
        printf("      10 blocks: %6d\n", measurements[1]);
        printf("     100 blocks: %7d\n", measurements[2]);
        printf("    1000 blocks: %8d\n", measurements[3]);
        printf("    cycles/byte: %7.2f\n", cpb[0]);
    }
    else if (numberOfColumns == 2) {
        printf("     laneCount:  %5d       %5d\n", laneCounts[0], laneCounts[1]);
        printf("       1 block:  %5d       %5d\n", measurements[0], measurements[4]);
        printf("      10 blocks: %6d      %6d\n", measurements[1], measurements[5]);
        printf("     100 blocks: %7d     %7d\n", measurements[2], measurements[6]);
        printf("    1000 blocks: %8d    %8d\n", measurements[3], measurements[7]);
        printf("    cycles/byte: %7.2f     %7.2f\n", cpb[0], cpb[1]);
    }
    else if (numberOfColumns == 3) {
        printf("     laneCount:  %5d       %5d       %5d\n", laneCounts[0], laneCounts[1], laneCounts[2]);
        printf("       1 block:  %5d       %5d       %5d\n", measurements[0], measurements[4], measurements[8]);
        printf("      10 blocks: %6d      %6d      %6d\n", measurements[1], measurements[5], measurements[9]);
        printf("     100 blocks: %7d     %7d     %7d\n", measurements[2], measurements[6], measurements[10]);
        printf("    1000 blocks: %8d    %8d    %8d\n", measurements[3], measurements[7], measurements[11]);
        printf("    cycles/byte: %7.2f     %7.2f     %7.2f\n", cpb[0], cpb[1], cpb[2]);
    }
    else if (numberOfColumns == 4) {
        printf("     laneCount:  %5d       %5d       %5d       %5d\n", laneCounts[0], laneCounts[1], laneCounts[2], laneCounts[3]);
        printf("       1 block:  %5d       %5d       %5d       %5d\n", measurements[0], measurements[4], measurements[8], measurements[12]);
        printf("      10 blocks: %6d      %6d      %6d      %6d\n", measurements[1], measurements[5], measurements[9], measurements[13]);
        printf("     100 blocks: %7d     %7d     %7d     %7d\n", measurements[2], measurements[6], measurements[10], measurements[14]);
        printf("    1000 blocks: %8d    %8d    %8d    %8d\n", measurements[3], measurements[7], measurements[11], measurements[15]);
        printf("    cycles/byte: %7.2f     %7.2f     %7.2f     %7.2f\n", cpb[0], cpb[1], cpb[2], cpb[3]);
    }
    printf("\n");
}
