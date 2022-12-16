/*
The eXtended Keccak Code Package (XKCP)
https://github.com/XKCP/XKCP

Implementation by Gilles Van Assche and Ronny Van Keer, hereby denoted as "the implementer".

For more information, feedback or questions, please refer to the Keccak Team website:
https://keccak.team/

To the extent possible under law, the implementer has waived all copyright
and related or neighboring rights to the source code in this file.
http://creativecommons.org/publicdomain/zero/1.0/
*/

#include <stdio.h>
#include "displayIntermediateValues.h"

FILE *intermediateValueFile = 0;
int displayLevel = 0;

void displaySetIntermediateValueFile(FILE *f)
{
    intermediateValueFile = f;
}

void displaySetLevel(int level)
{
    displayLevel = level;
}

void displayBytes(int level, const char *text, const unsigned char *bytes, unsigned int size)
{
    unsigned int i;

    if ((intermediateValueFile) && (level <= displayLevel)) {
        fprintf(intermediateValueFile, "%s:\n", text);
        for(i=0; i<size; i++)
            fprintf(intermediateValueFile, "%02X ", bytes[i]);
        fprintf(intermediateValueFile, "\n");
        fprintf(intermediateValueFile, "\n");
    }
}

void displayBits(int level, const char *text, const unsigned char *data, unsigned int size, int MSBfirst)
{
    unsigned int i, iByte, iBit;

    if ((intermediateValueFile) && (level <= displayLevel)) {
        fprintf(intermediateValueFile, "%s:\n", text);
        for(i=0; i<size; i++) {
            iByte = i/8;
            iBit = i%8;
            if (MSBfirst)
                fprintf(intermediateValueFile, "%d ", ((data[iByte] << iBit) & 0x80) != 0);
            else
                fprintf(intermediateValueFile, "%d ", ((data[iByte] >> iBit) & 0x01) != 0);
        }
        fprintf(intermediateValueFile, "\n");
        fprintf(intermediateValueFile, "\n");
    }
}

void displayStateAsBytes(int level, const char *text, const unsigned char *state, unsigned int width)
{
    displayBytes(level, text, state, width/8);
}

void displayStateAs32bitWords(int level, const char *text, const unsigned int *state)
{
    unsigned int i;

    if ((intermediateValueFile) && (level <= displayLevel)) {
        fprintf(intermediateValueFile, "%s:\n", text);
        for(i=0; i<25; i++) {
            fprintf(intermediateValueFile, "%08X:%08X", (unsigned int)state[2*i+0], (unsigned int)state[2*i+1]);
            if ((i%5) == 4)
                fprintf(intermediateValueFile, "\n");
            else
                fprintf(intermediateValueFile, " ");
        }
    }
}

void displayStateAs64bitLanes(int level, const char *text, void *statePointer)
{
    unsigned int i;
    unsigned long long int *state = statePointer;

    if ((intermediateValueFile) && (level <= displayLevel)) {
        fprintf(intermediateValueFile, "%s:\n", text);
        for(i=0; i<25; i++) {
            fprintf(intermediateValueFile, "%08X", (unsigned int)(state[i] >> 32));
            fprintf(intermediateValueFile, "%08X", (unsigned int)(state[i] & 0xFFFFFFFFULL));
            if ((i%5) == 4)
                fprintf(intermediateValueFile, "\n");
            else
                fprintf(intermediateValueFile, " ");
        }
    }
}

void displayStateAs32bitLanes(int level, const char *text, void *statePointer)
{
    unsigned int i;
    unsigned int *state = statePointer;

    if ((intermediateValueFile) && (level <= displayLevel)) {
        fprintf(intermediateValueFile, "%s:\n", text);
        for(i=0; i<25; i++) {
            fprintf(intermediateValueFile, "%08X", state[i]);
            if ((i%5) == 4)
                fprintf(intermediateValueFile, "\n");
            else
                fprintf(intermediateValueFile, " ");
        }
    }
}

void displayStateAs16bitLanes(int level, const char *text, void *statePointer)
{
    unsigned int i;
    unsigned short *state = statePointer;

    if ((intermediateValueFile) && (level <= displayLevel)) {
        fprintf(intermediateValueFile, "%s:\n", text);
        for(i=0; i<25; i++) {
            fprintf(intermediateValueFile, "%04X ", state[i]);
            if ((i%5) == 4)
                fprintf(intermediateValueFile, "\n");
        }
    }
}

void displayStateAs8bitLanes(int level, const char *text, void *statePointer)
{
    unsigned int i;
    unsigned char *state = statePointer;

    if ((intermediateValueFile) && (level <= displayLevel)) {
        fprintf(intermediateValueFile, "%s:\n", text);
        for(i=0; i<25; i++) {
            fprintf(intermediateValueFile, "%02X ", state[i]);
            if ((i%5) == 4)
                fprintf(intermediateValueFile, "\n");
        }
    }
}

void displayStateAsLanes(int level, const char *text, void *statePointer, unsigned int width)
{
    if (width == 1600)
        displayStateAs64bitLanes(level, text, statePointer);
    if (width == 800)
        displayStateAs32bitLanes(level, text, statePointer);
    if (width == 400)
        displayStateAs16bitLanes(level, text, statePointer);
    if (width == 200)
        displayStateAs8bitLanes(level, text, statePointer);
}

void displayRoundNumber(int level, unsigned int i)
{
    if ((intermediateValueFile) && (level <= displayLevel)) {
        fprintf(intermediateValueFile, "\n");
        fprintf(intermediateValueFile, "--- Round %d ---\n", i);
        fprintf(intermediateValueFile, "\n");
    }
}

void displayText(int level, const char *text)
{
    if ((intermediateValueFile) && (level <= displayLevel)) {
        fprintf(intermediateValueFile, "%s", text);
        fprintf(intermediateValueFile, "\n");
        fprintf(intermediateValueFile, "\n");
    }
}
