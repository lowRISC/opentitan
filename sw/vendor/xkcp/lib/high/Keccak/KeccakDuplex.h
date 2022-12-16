/*
The eXtended Keccak Code Package (XKCP)
https://github.com/XKCP/XKCP

Keccak, designed by Guido Bertoni, Joan Daemen, Michaël Peeters and Gilles Van Assche.

Implementation by the designers, hereby denoted as "the implementer".

For more information, feedback or questions, please refer to the Keccak Team website:
https://keccak.team/

To the extent possible under law, the implementer has waived all copyright
and related or neighboring rights to the source code in this file.
http://creativecommons.org/publicdomain/zero/1.0/
*/

#ifndef _KeccakDuplex_h_
#define _KeccakDuplex_h_

/* For the documentation, please follow the link: */
/* #include "KeccakDuplex-documentation.h" */

#include <string.h>
#include "align.h"
#include "config.h"

#define XKCP_DeclareDuplexStructure(prefix, size, alignment) \
    ALIGN(alignment) typedef struct prefix##_DuplexInstanceStruct { \
        unsigned char state[size]; \
        unsigned int rate; \
        unsigned int byteInputIndex; \
        unsigned int byteOutputIndex; \
    } prefix##_DuplexInstance;

#define XKCP_DeclareDuplexFunctions(prefix) \
    int prefix##_DuplexInitialize(prefix##_DuplexInstance *duplexInstance, unsigned int rate, unsigned int capacity); \
    int prefix##_Duplexing(prefix##_DuplexInstance *duplexInstance, const unsigned char *sigmaBegin, unsigned int sigmaBeginByteLen, unsigned char *Z, unsigned int ZByteLen, unsigned char delimitedSigmaEnd); \
    int prefix##_DuplexingFeedPartialInput(prefix##_DuplexInstance *duplexInstance, const unsigned char *input, unsigned int inputByteLen); \
    int prefix##_DuplexingFeedZeroes(prefix##_DuplexInstance *duplexInstance, unsigned int inputByteLen); \
    int prefix##_DuplexingOverwritePartialInput(prefix##_DuplexInstance *duplexInstance, const unsigned char *input, unsigned int inputByteLen); \
    int prefix##_DuplexingOverwriteWithZeroes(prefix##_DuplexInstance *duplexInstance, unsigned int inputByteLen); \
    int prefix##_DuplexingGetFurtherOutput(prefix##_DuplexInstance *duplexInstance, unsigned char *out, unsigned int outByteLen); \
    int prefix##_DuplexingGetFurtherOutputAndAdd(prefix##_DuplexInstance *duplexInstance, const unsigned char *input, unsigned char *output, unsigned int outputByteLen);

#ifdef XKCP_has_KeccakP200
    #include "KeccakP-200-SnP.h"
    XKCP_DeclareDuplexStructure(KeccakWidth200, KeccakP200_stateSizeInBytes, KeccakP200_stateAlignment)
    XKCP_DeclareDuplexFunctions(KeccakWidth200)
    #define XKCP_has_Duplex_Keccak_width200
#endif

#ifdef XKCP_has_KeccakP400
    #include "KeccakP-400-SnP.h"
    XKCP_DeclareDuplexStructure(KeccakWidth400, KeccakP400_stateSizeInBytes, KeccakP400_stateAlignment)
    XKCP_DeclareDuplexFunctions(KeccakWidth400)
    #define XKCP_has_Duplex_Keccak_width400
#endif

#ifdef XKCP_has_KeccakP800
    #include "KeccakP-800-SnP.h"
    XKCP_DeclareDuplexStructure(KeccakWidth800, KeccakP800_stateSizeInBytes, KeccakP800_stateAlignment)
    XKCP_DeclareDuplexFunctions(KeccakWidth800)
    #define XKCP_has_Duplex_Keccak_width800
#endif

#ifdef XKCP_has_KeccakP1600
    #include "KeccakP-1600-SnP.h"
    XKCP_DeclareDuplexStructure(KeccakWidth1600, KeccakP1600_stateSizeInBytes, KeccakP1600_stateAlignment)
    XKCP_DeclareDuplexFunctions(KeccakWidth1600)
    #define XKCP_has_Duplex_Keccak_width1600
#endif

#endif
