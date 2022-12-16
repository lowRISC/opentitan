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

#ifndef _KeccakPRG_h_
#define _KeccakPRG_h_

/* For the documentation, please follow the link: */
/* #include "KeccakPRG-documentation.h" */

#include <string.h>
#include "align.h"
#include "config.h"
#include "KeccakDuplex.h"

#define XKCP_DeclareSpongePRG_Structure(prefix, size, alignment) \
    ALIGN(alignment) typedef struct prefix##_SpongePRG_InstanceStruct { \
        prefix##_DuplexInstance duplex; \
    } prefix##_SpongePRG_Instance;

#define XKCP_DeclareSpongePRG_Functions(prefix) \
    int prefix##_SpongePRG_Initialize(prefix##_SpongePRG_Instance *instance, unsigned int capacity); \
    int prefix##_SpongePRG_Feed(prefix##_SpongePRG_Instance *instance, const unsigned char *input, unsigned int inputByteLen); \
    int prefix##_SpongePRG_Fetch(prefix##_SpongePRG_Instance *Instance, unsigned char *out, unsigned int outByteLen); \
    int prefix##_SpongePRG_Forget(prefix##_SpongePRG_Instance *instance);

#ifdef XKCP_has_KeccakP200
    #include "KeccakP-200-SnP.h"
    XKCP_DeclareSpongePRG_Structure(KeccakWidth200, KeccakP200_stateSizeInBytes, KeccakP200_stateAlignment)
    XKCP_DeclareSpongePRG_Functions(KeccakWidth200)
    #define XKCP_has_PRG_Keccak_width200
#endif

#ifdef XKCP_has_KeccakP400
    #include "KeccakP-400-SnP.h"
    XKCP_DeclareSpongePRG_Structure(KeccakWidth400, KeccakP400_stateSizeInBytes, KeccakP400_stateAlignment)
    XKCP_DeclareSpongePRG_Functions(KeccakWidth400)
    #define XKCP_has_PRG_Keccak_width400
#endif

#ifdef XKCP_has_KeccakP800
    #include "KeccakP-800-SnP.h"
    XKCP_DeclareSpongePRG_Structure(KeccakWidth800, KeccakP800_stateSizeInBytes, KeccakP800_stateAlignment)
    XKCP_DeclareSpongePRG_Functions(KeccakWidth800)
    #define XKCP_has_PRG_Keccak_width800
#endif

#ifdef XKCP_has_KeccakP1600
    #include "KeccakP-1600-SnP.h"
    XKCP_DeclareSpongePRG_Structure(KeccakWidth1600, KeccakP1600_stateSizeInBytes, KeccakP1600_stateAlignment)
    XKCP_DeclareSpongePRG_Functions(KeccakWidth1600)
    #define XKCP_has_PRG_Keccak_width1600
#endif

#endif
