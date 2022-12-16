/*
The eXtended Keccak Code Package (XKCP)
https://github.com/XKCP/XKCP

Keccak, designed by Guido Bertoni, Joan Daemen, Michaël Peeters and Gilles Van Assche.

Implementation by Ronny Van Keer, hereby denoted as "the implementer".

For more information, feedback or questions, please refer to the Keccak Team website:
https://keccak.team/

To the extent possible under law, the implementer has waived all copyright
and related or neighboring rights to the source code in this file.
http://creativecommons.org/publicdomain/zero/1.0/
*/

#include <string.h>
#include "SP800-185.h"

#ifdef XKCP_has_KeccakP1600times2
    #include "KeccakP-1600-times2-SnP.h"
#endif

#ifdef XKCP_has_KeccakP1600times4
    #include "KeccakP-1600-times4-SnP.h"
#endif

#ifdef XKCP_has_KeccakP1600times8
    #include "KeccakP-1600-times8-SnP.h"
#endif

/* #define DEBUG_DUMP */

#if defined(DEBUG_DUMP)

#include <stdio.h>

static void DUMP( const unsigned char * pText, const unsigned char * pData, unsigned int size )
{
    unsigned int i;
    printf("%s (%u bytes):", pText, size);
    for(i=0; i<size; i++)
        printf(" %02x", (int)pData[i]);
    printf("\n");
}
#else
#define DUMP(pText, pData, size )
#endif

static unsigned int left_encode( unsigned char * encbuf, size_t value )
{
    unsigned int n, i;
    size_t v;

    for ( v = value, n = 0; v && (n < sizeof(size_t)); ++n, v >>= 8 )
        ; /* empty */
    if (n == 0)
        n = 1;
    for ( i = 1; i <= n; ++i )
    {
        encbuf[i] = (unsigned char)(value >> (8 * (n-i)));
    }
    encbuf[0] = (unsigned char)n;
    return n + 1;
}

static unsigned int right_encode( unsigned char * encbuf, size_t value )
{
    unsigned int n, i;
    size_t v;

    for ( v = value, n = 0; v && (n < sizeof(size_t)); ++n, v >>= 8 )
        ; /* empty */
    if (n == 0)
        n = 1;
    for ( i = 1; i <= n; ++i )
    {
        encbuf[i-1] = (unsigned char)(value >> (8 * (n-i)));
    }
    encbuf[n] = (unsigned char)n;
    return n + 1;
}

#define laneSize        8
#define suffix          0x1F

#define security        128
#include "SP800-185.inc"
#undef  security

#define security        256
#include "SP800-185.inc"
#undef  security
