/*
The eXtended Keccak Code Package (XKCP)
https://github.com/XKCP/XKCP

Keccak, designed by Guido Bertoni, Joan Daemen, Michaël Peeters and Gilles Van Assche.

Implementation by Gilles Van Assche, hereby denoted as "the implementer".

For more information, feedback or questions, please refer to the Keccak Team website:
https://keccak.team/

To the extent possible under law, the implementer has waived all copyright
and related or neighboring rights to the source code in this file.
http://creativecommons.org/publicdomain/zero/1.0/
*/

#include "KeccakPRG.h"

#ifdef KeccakReference
    #include "displayIntermediateValues.h"
#endif

#ifdef XKCP_has_KeccakP200
    #include "KeccakP-200-SnP.h"

    #define prefix KeccakWidth200
    #define SnP_width 200
        #include "KeccakPRG.inc"
    #undef prefix
    #undef SnP_width
#endif

#ifdef XKCP_has_KeccakP400
    #include "KeccakP-400-SnP.h"

    #define prefix KeccakWidth400
    #define SnP_width 400
        #include "KeccakPRG.inc"
    #undef prefix
    #undef SnP_width
#endif

#ifdef XKCP_has_KeccakP800
    #include "KeccakP-800-SnP.h"

    #define prefix KeccakWidth800
    #define SnP_width 800
        #include "KeccakPRG.inc"
    #undef prefix
    #undef SnP_width
#endif

#ifdef XKCP_has_KeccakP1600
    #include "KeccakP-1600-SnP.h"

    #define prefix KeccakWidth1600
    #define SnP_width 1600
        #include "KeccakPRG.inc"
    #undef prefix
    #undef SnP_width
#endif
