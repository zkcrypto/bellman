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
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "testKangarooTwelve.h"
#include "testPerformance.h"

void printHelp()
{
        printf("Usage: KeccakTests command(s), where the commands can be\n");
        printf("  --help or -h              To display this page\n");
        printf("  --all or -a               All tests\n");
        printf("  --KangarooTwelve or -K12  Tests on KangarooTwelve\n");
        printf("  --speed or -s             Speed measuresments\n");
}

int process(int argc, char* argv[])
{
    int i;
    int help = 0;
    int KangarooTwelve = 0;
    int speed = 0;

    if (argc == 1)
        help = 1;

    for(i=1; i<argc; i++) {
        if ((strcmp("--help", argv[i]) == 0) || (strcmp("-h", argv[i]) == 0))
            help = 1;
        else if ((strcmp("--all", argv[i]) == 0) || (strcmp("-a", argv[i]) == 0))
           KangarooTwelve = speed = 1;
        else if ((strcmp("--KangarooTwelve", argv[i]) == 0) || (strcmp("-K12", argv[i]) == 0))
            KangarooTwelve = 1;
        else if ((strcmp("--speed", argv[i]) == 0) || (strcmp("-s", argv[i]) == 0))
            speed = 1;
        else {
            printf("Unrecognized command '%s'\n", argv[i]);
            return -1;
        }
    }
    if (help) {
        printHelp();
        return 0;
    }
    if (KangarooTwelve) {
        testKangarooTwelve();
    }
    if (speed) {
        testPerformance();
    }
    return 0;
}

int main(int argc, char* argv[])
{
    return process(argc, argv);
}
