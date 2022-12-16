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

#ifndef _displayIntermediateValues_h_
#define _displayIntermediateValues_h_

#include <stdio.h>

void displaySetIntermediateValueFile(FILE *f);
void displaySetLevel(int level);
void displayBytes(int level, const char *text, const unsigned char *bytes, unsigned int size);
void displayBits(int level, const char *text, const unsigned char *data, unsigned int size, int MSBfirst);
void displayStateAsBytes(int level, const char *text, const unsigned char *state, unsigned int width);
void displayStateAs32bitWords(int level, const char *text, const unsigned int *state);
void displayStateAsLanes(int level, const char *text, void *statePointer, unsigned int width);
void displayRoundNumber(int level, unsigned int i);
void displayText(int level, const char *text);

#endif
