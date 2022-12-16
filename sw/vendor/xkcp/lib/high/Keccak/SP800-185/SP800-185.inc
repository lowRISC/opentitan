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

#define JOIN0(a, b)             a ## b
#define JOIN(a, b)              JOIN0(a, b)

#define capacity        (2*security)
#define capacityInBytes (capacity/8)
#define capacityInLanes (capacityInBytes/laneSize)
#define rate            (1600-capacity)
#define rateInBytes     (rate/8)
#define rateInLanes     (rateInBytes/laneSize)


#define cSHAKE              JOIN(cSHAKE,security)
#define cSHAKE_Initialize   JOIN(cSHAKE,_Initialize)
#define cSHAKE_Update       JOIN(cSHAKE,_Update)
#define cSHAKE_Final        JOIN(cSHAKE,_Final)
#define cSHAKE_Squeeze      JOIN(cSHAKE,_Squeeze)

int cSHAKE_Initialize(cSHAKE_Instance *csk, BitLength outputBitLen, const BitSequence *name, BitLength nameBitLen, const BitSequence *customization, BitLength customBitLen)
{
    unsigned char encbuf[sizeof(BitLength)+1];

    /* Only full bytes are supported for 'name', otherwise customization string would have to be shifted before absorbing */
    if ((nameBitLen & 7) != 0)
        return 1;
    if (KeccakWidth1600_SpongeInitialize(&csk->sponge, rate, capacity) != 0)
        return 1;
    csk->lastByteBitLen = 0;
    csk->lastByteValue = 0;
    csk->fixedOutputLength = outputBitLen;
    csk->phase = ABSORBING;

    if ((nameBitLen == 0) && (customBitLen == 0))
        csk->emptyNameCustom = 1;
    else
    {
        csk->emptyNameCustom = 0;

        /* Absorb bytepad(.., rate) */
        if (KeccakWidth1600_SpongeAbsorb(&csk->sponge, encbuf, left_encode(encbuf, rateInBytes)) != 0)
            return 1;

        /* Absorb encode_string(name) */
        if (KeccakWidth1600_SpongeAbsorb(&csk->sponge, encbuf, left_encode(encbuf, nameBitLen)) != 0)
            return 1;
        if (KeccakWidth1600_SpongeAbsorb(&csk->sponge, name, nameBitLen / 8) != 0)
            return 1;

        /* Absorb encode_string(customization) */
        if (KeccakWidth1600_SpongeAbsorb(&csk->sponge, encbuf, left_encode(encbuf, customBitLen)) != 0)
            return 1;
        if (KeccakWidth1600_SpongeAbsorb(&csk->sponge, customization, (customBitLen + 7) / 8) != 0) /* allowed to be a bit string, as zero padding is following */
            return 1;
            
        /* Zero padding up to rate */
        if ( csk->sponge.byteIOIndex != 0 ) {
            csk->sponge.byteIOIndex = rateInBytes - 1;
            encbuf[0] = 0;
            return KeccakWidth1600_SpongeAbsorb(&csk->sponge, encbuf, 1);
        }
    }
    return 0;
}

int cSHAKE_Update(cSHAKE_Instance *csk, const BitSequence *input, BitLength inputBitLen)
{

    if (csk->phase != ABSORBING)
        return 1;
    if (csk->lastByteBitLen != 0)    /* check if previous call input were full bytes */
        return 1;
    csk->lastByteBitLen = inputBitLen & 7;
    if(csk->lastByteBitLen != 0)
        csk->lastByteValue = input[inputBitLen / 8] & ((1 << csk->lastByteBitLen) - 1); /* strip unwanted bits */
    return KeccakWidth1600_SpongeAbsorb(&csk->sponge, input, inputBitLen / 8);
}

int cSHAKE_Final(cSHAKE_Instance *csk, BitSequence *output)
{
    unsigned short delimitedLastBytes;
    unsigned char delimitedSuffix;

    if (csk->phase != ABSORBING)
        return 1;

    /* Concatenate the last few input bits with those of the suffix */
    if (csk->emptyNameCustom != 0)
        delimitedLastBytes = (unsigned short)(csk->lastByteValue | (0x1F << csk->lastByteBitLen));
    else
        delimitedLastBytes = (unsigned short)(csk->lastByteValue | (0x04 << csk->lastByteBitLen)); /* Suffix '04': 2 zero bits '00' */
    if ((delimitedLastBytes >> 8) == 0) {
        delimitedSuffix = (unsigned char)delimitedLastBytes;
    }
    else {
        unsigned char oneByte[1];
        oneByte[0] = (unsigned char)delimitedLastBytes;
        if(KeccakWidth1600_SpongeAbsorb(&csk->sponge, oneByte, 1) != 0)
            return 1;
        delimitedSuffix = (unsigned char)(delimitedLastBytes >> 8);
    }
    if (KeccakWidth1600_SpongeAbsorbLastFewBits(&csk->sponge, delimitedSuffix) != 0) 
        return 1;
    csk->phase = SQUEEZING;
    if ( csk->fixedOutputLength != 0 ) {
        if(cSHAKE_Squeeze(csk, output, csk->fixedOutputLength) != 0)
            return 1;
        csk->phase = FINAL;
    }
    return 0;
}

int cSHAKE_Squeeze(cSHAKE_Instance *csk, BitSequence *output, BitLength outputBitLen)
{
    if (csk->phase != SQUEEZING)
        return 1;
    if(KeccakWidth1600_SpongeSqueeze(&csk->sponge, output, (outputBitLen + 7) / 8) != 0)
        return 1;
    if ((outputBitLen & 7) !=0) {
        output[outputBitLen / 8] &= (1 << (outputBitLen & 7)) - 1; /* clear unwanted bits */
        csk->phase = FINAL; /* only last output can have an non complete byte, block nexts calls */
    }
    return 0;
}

int cSHAKE( const BitSequence *input, BitLength inputBitLen, BitSequence *output, BitLength outputBitLen, 
        const BitSequence *name, BitLength nameBitLen, const BitSequence *customization, BitLength customBitLen )
{
    cSHAKE_Instance csk;

    if (outputBitLen == 0)
        return 1;
    if (cSHAKE_Initialize(&csk, outputBitLen, name, nameBitLen, customization, customBitLen) != 0)
        return 1;
    if (cSHAKE_Update(&csk, input, inputBitLen) != 0)
        return 1;
    return cSHAKE_Final(&csk, output);
}

/* ------------------------------------------------------------------------- */

#define KMAC              JOIN(KMAC,security)
#define KMAC_Initialize   JOIN(KMAC,_Initialize)
#define KMAC_Update       JOIN(KMAC,_Update)
#define KMAC_Final        JOIN(KMAC,_Final)
#define KMAC_Squeeze      JOIN(KMAC,_Squeeze)

int KMAC_Initialize(KMAC_Instance *km, const BitSequence *key, BitLength keyBitLen, BitLength outputBitLen, const BitSequence *customization, BitLength customBitLen)
{
    BitLength   bufferLen;
    BitLength   keyByteLen;
    BitSequence buffer[rateInBytes];

    if (cSHAKE_Initialize(&km->csi, outputBitLen, (const BitSequence*)"KMAC", 4*8, customization, customBitLen) != 0)
        return 1;
    km->outputBitLen = outputBitLen;

    /* bytepad(encode_string(k)) */
    bufferLen = left_encode(buffer, rateInBytes);
    bufferLen += left_encode(buffer + bufferLen, keyBitLen);
    if (cSHAKE_Update(&km->csi, buffer, bufferLen*8) != 0)
        return 1;
    keyByteLen = (keyBitLen + 7) / 8;
    if (cSHAKE_Update(&km->csi, key, keyByteLen*8) != 0)
        return 1;
    bufferLen = (bufferLen + keyByteLen) % rateInBytes; /* zero padding */
    if (bufferLen != 0) {
        bufferLen = rateInBytes - bufferLen;
        memset(buffer, 0, bufferLen);
        if (cSHAKE_Update(&km->csi, buffer, bufferLen*8) != 0)
            return 1;
    }
    return 0;
}

int KMAC_Update(KMAC_Instance *km, const BitSequence *input, BitLength inputBitLen)
{
    if ((inputBitLen & 7) != 0) /* Only full bytes are supported */
        return 1;
    return cSHAKE_Update(&km->csi, input, inputBitLen);
}

int KMAC_Final(KMAC_Instance *km, BitSequence *output)
{
    unsigned char encbuf[sizeof(BitLength)+1];

    if (cSHAKE_Update(&km->csi, encbuf, right_encode(encbuf, km->outputBitLen)*8) != 0)
        return 1;
    return cSHAKE_Final(&km->csi, output);
}

int KMAC_Squeeze(KMAC_Instance *km, BitSequence *output, BitLength outputBitLen)
{
    return cSHAKE_Squeeze(&km->csi, output, outputBitLen);
}

int KMAC(const BitSequence *key, BitLength keyBitLen, const BitSequence *input, BitLength inputBitLen,
        BitSequence *output, BitLength outputBitLen, const BitSequence *customization, BitLength customBitLen)
{
    KMAC_Instance km;

    if (outputBitLen == 0)
        return 1;
    if (KMAC_Initialize(&km, key, keyBitLen, outputBitLen, customization, customBitLen) != 0)
        return 1;
    if (KMAC_Update(&km, input, inputBitLen) != 0)
        return 1;
    return KMAC_Final(&km, output);
}

#undef  KMAC_Initialize
#undef  KMAC_Update
#undef  KMAC_Final
#undef  KMAC_Squeeze
#undef  KMAC

/* ------------------------------------------------------------------------- */

#define ParallelHash              JOIN(ParallelHash,security)
#define ParallelHash_Initialize   JOIN(ParallelHash,_Initialize)
#define ParallelHash_Update       JOIN(ParallelHash,_Update)
#define ParallelHash_Final        JOIN(ParallelHash,_Final)
#define ParallelHash_Squeeze      JOIN(ParallelHash,_Squeeze)

#define ParallelSpongeFastLoop( Parallellism ) \
    while ( inputByteLen >= Parallellism * phi->blockLen ) { \
        ALIGN(KeccakP1600times##Parallellism##_statesAlignment) unsigned char states[KeccakP1600times##Parallellism##_statesSizeInBytes]; \
        unsigned char intermediate[Parallellism*capacityInBytes]; \
        size_t localBlockLen = phi->blockLen; \
        const unsigned char * localInput = input; \
        unsigned int i; \
        size_t fastLoopOffset; \
        \
        KeccakP1600times##Parallellism##_StaticInitialize(); \
        KeccakP1600times##Parallellism##_InitializeAll(states); \
        fastLoopOffset = KeccakF1600times##Parallellism##_FastLoop_Absorb(states, rateInLanes, phi->blockLen / laneSize, rateInLanes, localInput, Parallellism * phi->blockLen); \
        localBlockLen -= fastLoopOffset; \
        localInput += fastLoopOffset; \
        for ( i = 0; i < Parallellism; ++i, localInput += phi->blockLen ) { \
            KeccakP1600times##Parallellism##_AddBytes(states, i, localInput, 0, localBlockLen); \
            KeccakP1600times##Parallellism##_AddByte(states, i, suffix, localBlockLen); \
            KeccakP1600times##Parallellism##_AddByte(states, i, 0x80, rateInBytes-1); \
        } \
        KeccakP1600times##Parallellism##_PermuteAll_24rounds(states); \
        input += Parallellism * phi->blockLen; \
        inputByteLen -= Parallellism * phi->blockLen; \
        KeccakP1600times##Parallellism##_ExtractLanesAll(states, intermediate, capacityInLanes, capacityInLanes ); \
        if (KeccakWidth1600_SpongeAbsorb(&phi->finalNode, intermediate, Parallellism * capacityInBytes) != 0) return 1; \
    }

#define ParallelSpongeLoop( Parallellism ) \
    while ( inputByteLen >= Parallellism * phi->blockLen ) { \
        ALIGN(KeccakP1600times##Parallellism##_statesAlignment) unsigned char states[KeccakP1600times##Parallellism##_statesSizeInBytes]; \
        unsigned char intermediate[Parallellism*capacityInBytes]; \
        size_t localBlockLen = phi->blockLen; \
        const unsigned char * localInput = input; \
        unsigned int i; \
        \
        KeccakP1600times##Parallellism##_StaticInitialize(); \
        KeccakP1600times##Parallellism##_InitializeAll(states); \
        while(localBlockLen >= rateInBytes) { \
            KeccakP1600times##Parallellism##_AddLanesAll(states, localInput, rateInLanes, phi->blockLen / laneSize); \
            KeccakP1600times##Parallellism##_PermuteAll_24rounds(states); \
            localBlockLen -= rateInBytes; \
            localInput += rateInBytes; \
        } \
        for ( i = 0; i < Parallellism; ++i, localInput += phi->blockLen ) { \
            KeccakP1600times##Parallellism##_AddBytes(states, i, localInput, 0, localBlockLen); \
            KeccakP1600times##Parallellism##_AddByte(states, i, suffix, localBlockLen); \
            KeccakP1600times##Parallellism##_AddByte(states, i, 0x80, rateInBytes-1); \
        } \
        KeccakP1600times##Parallellism##_PermuteAll_24rounds(states); \
        input += Parallellism * phi->blockLen; \
        inputByteLen -= Parallellism * phi->blockLen; \
        KeccakP1600times##Parallellism##_ExtractLanesAll(states, intermediate, capacityInLanes, capacityInLanes ); \
        if (KeccakWidth1600_SpongeAbsorb(&phi->finalNode, intermediate, Parallellism * capacityInBytes) != 0) return 1; \
    }

int ParallelHash_Initialize(ParallelHash_Instance *phi, size_t blockByteLen,
        BitLength outputBitLen, const BitSequence *customization, BitLength customBitLen)
{
    size_t t;
    unsigned char encbuf[sizeof(size_t)+1];

    if ( blockByteLen < laneSize)   /* blockLen must be greater than or equal to lane size */
        return 1;
    for ( t = blockByteLen; t > 1; t >>= 1 )  /* blockLen (in bytes) must be a power of two */
        if ( (t & 1) && (t != 1) )  /* bit0 set and other bits unset */
            return 1;
    if (KeccakWidth1600_SpongeInitialize(&phi->finalNode, rate, capacity) != 0)
        return 1;
    phi->fixedOutputLength = outputBitLen;
    phi->blockLen = blockByteLen;
    phi->queueAbsorbedLen = 0;
    phi->totalInputSize = 0;
    phi->phase = ABSORBING;

    /* Absorb bytepad(.., rate) */
    if (KeccakWidth1600_SpongeAbsorb(&phi->finalNode, encbuf, left_encode(encbuf, rateInBytes)) != 0)
        return 1;

    /* Absorb string_encode("ParallelHash") */
    if (KeccakWidth1600_SpongeAbsorb(&phi->finalNode, (const BitSequence*)"\x01\x60" "ParallelHash", 14) != 0)
        return 1;

    /* Absorb string_encode(customization) */
    if (KeccakWidth1600_SpongeAbsorb(&phi->finalNode, encbuf, left_encode(encbuf, customBitLen)) != 0)
        return 1;
    if (KeccakWidth1600_SpongeAbsorb(&phi->finalNode, customization, (customBitLen + 7) / 8) != 0)
        return 1;
        
    /* Zero padding up to rate */
    if ( phi->finalNode.byteIOIndex != 0 ) {
        phi->finalNode.byteIOIndex = rateInBytes - 1;
        encbuf[0] = 0;
        if (KeccakWidth1600_SpongeAbsorb(&phi->finalNode, encbuf, 1) != 0)
            return 1;
    }

    /* Absorb B */
    if (KeccakWidth1600_SpongeAbsorb(&phi->finalNode, encbuf, left_encode(encbuf, blockByteLen)) != 0) 
        return 1;
    return 0;
}

int ParallelHash_Update(ParallelHash_Instance *phi, const BitSequence *input, BitLength inputBitLen)
{
    size_t    inputByteLen;

    if (phi->phase != ABSORBING)
        return 1;
    if ((inputBitLen & 7) != 0) /* Only full bytes are supported */
        return 1;
    phi->totalInputSize += inputBitLen;
    inputByteLen = inputBitLen / 8;
    if ( phi->queueAbsorbedLen != 0 ) {
        /* There is data in the queue, absorb further in queue until full */
        size_t len = (inputByteLen < (phi->blockLen - phi->queueAbsorbedLen)) ? inputByteLen : (phi->blockLen - phi->queueAbsorbedLen);
        if (KeccakWidth1600_SpongeAbsorb(&phi->queueNode, input, len) != 0)
            return 1;
        input += len;
        inputByteLen -= len;
        phi->queueAbsorbedLen += len;
        if ( phi->queueAbsorbedLen == phi->blockLen ) {
            unsigned char intermediate[capacityInBytes];
            phi->queueAbsorbedLen = 0;
            if (KeccakWidth1600_SpongeAbsorbLastFewBits(&phi->queueNode, suffix) != 0)
                return 1;
            if (KeccakWidth1600_SpongeSqueeze(&phi->queueNode, intermediate, capacityInBytes) != 0)
                return 1;
            if (KeccakWidth1600_SpongeAbsorb(&phi->finalNode, intermediate, capacityInBytes) != 0)
                return 1;
        }
    }

    #if defined(KeccakP1600times8_implementation) && !defined(KeccakP1600times8_isFallback)
    #if defined(KeccakF1600times8_FastLoop_supported)
    ParallelSpongeFastLoop( 8 )
    #else
    ParallelSpongeLoop( 8 )
    #endif
    #endif

    #if defined(KeccakP1600times4_implementation) && !defined(KeccakP1600times4_isFallback)
    #if defined(KeccakF1600times4_FastLoop_supported)
    ParallelSpongeFastLoop( 4 )
    #else
    ParallelSpongeLoop( 4 )
    #endif
    #endif

    #if defined(KeccakP1600times2_implementation) && !defined(KeccakP1600times2_isFallback)
    #if defined(KeccakF1600times2_FastLoop_supported)
    ParallelSpongeFastLoop( 2 )
    #else
    ParallelSpongeLoop( 2 )
    #endif
    #endif

    while ( inputByteLen > 0 ) {
        size_t len = (inputByteLen < phi->blockLen) ? inputByteLen : phi->blockLen;
        if (KeccakWidth1600_SpongeInitialize(&phi->queueNode, rate, capacity) != 0)
            return 1;
        if (KeccakWidth1600_SpongeAbsorb(&phi->queueNode, input, len) != 0)
            return 1;
        input += len;
        inputByteLen -= len;
        if ( len == phi->blockLen ) {
            unsigned char intermediate[capacityInBytes];
            if (KeccakWidth1600_SpongeAbsorbLastFewBits(&phi->queueNode, suffix) != 0)
                return 1;
            if (KeccakWidth1600_SpongeSqueeze(&phi->queueNode, intermediate, capacityInBytes) != 0)
                return 1;
            if (KeccakWidth1600_SpongeAbsorb(&phi->finalNode, intermediate, capacityInBytes) != 0)
                return 1;
        }
        else
            phi->queueAbsorbedLen = len;
    }

    return 0;
}

int ParallelHash_Final(ParallelHash_Instance *phi, BitSequence * output)
{
    unsigned char encbuf[sizeof(size_t)+1];
    size_t nBlocks;

    if (phi->phase != ABSORBING)
        return 1;
    if ( phi->queueAbsorbedLen != 0 ) {
        /* There is data in the queue */
        unsigned char intermediate[capacityInBytes];
        if (KeccakWidth1600_SpongeAbsorbLastFewBits(&phi->queueNode, suffix) != 0)
            return 1;
        if (KeccakWidth1600_SpongeSqueeze(&phi->queueNode, intermediate, capacityInBytes) != 0)
            return 1;
        if (KeccakWidth1600_SpongeAbsorb(&phi->finalNode, intermediate, capacityInBytes) != 0)
            return 1;
    }

    nBlocks = (phi->totalInputSize / 8 + phi->blockLen - 1) / phi->blockLen;
    if (KeccakWidth1600_SpongeAbsorb(&phi->finalNode, encbuf, right_encode(encbuf, nBlocks)) != 0) /* Absorb number of blocks */
        return 1;

    if (KeccakWidth1600_SpongeAbsorb(&phi->finalNode, encbuf, right_encode(encbuf, phi->fixedOutputLength)) != 0) /* Absorb output length in bits */
        return 1;

    if (KeccakWidth1600_SpongeAbsorbLastFewBits(&phi->finalNode, 0x04) != 0) /* Absorb 2 zero bits '00' */
        return 1;
    phi->phase = SQUEEZING;
    if ( phi->fixedOutputLength != 0 ) {
        if (ParallelHash_Squeeze(phi, output, phi->fixedOutputLength) != 0)
            return 1;
        phi->phase = FINAL;
    }
    return 0;
}

int ParallelHash_Squeeze(ParallelHash_Instance *phi, BitSequence *output, BitLength outputBitLen)
{
    if (phi->phase != SQUEEZING)
        return 1;
    if (KeccakWidth1600_SpongeSqueeze(&phi->finalNode, output, (outputBitLen + 7) / 8) != 0)
        return 1;
    if ((outputBitLen & 7) !=0) {
        output[outputBitLen / 8] &= (1 << (outputBitLen & 7)) - 1; /* clear unwanted bits */
        phi->phase = FINAL; /* only last output can have an non complete byte, block nexts calls */
    }
    return 0;
}

int ParallelHash( const BitSequence *input, BitLength inputBitLen, size_t blockByteLen,
        BitSequence *output, BitLength outputBitLen, const BitSequence *customization, BitLength customBitLen)
{
    ParallelHash_Instance phi;

    if (outputBitLen == 0)
        return 1;
    if (ParallelHash_Initialize(&phi, blockByteLen, outputBitLen, customization, customBitLen) != 0)
        return 1;
    if (ParallelHash_Update(&phi, input, inputBitLen) != 0)
        return 1;
    return ParallelHash_Final(&phi, output);
}

#undef  ParallelHash_Initialize
#undef  ParallelHash_Update
#undef  ParallelHash_Final
#undef  ParallelHash_Squeeze
#undef  ParallelHash

#undef  ParallelSpongeFastLoop
#undef  ParallelSpongeLoop

/* ------------------------------------------------------------------------- */

#define TupleHash              JOIN(TupleHash,security)
#define TupleHash_Initialize   JOIN(TupleHash,_Initialize)
#define TupleHash_Update       JOIN(TupleHash,_Update)
#define TupleHash_Final        JOIN(TupleHash,_Final)
#define TupleHash_Squeeze      JOIN(TupleHash,_Squeeze)

int TupleHash_Initialize(TupleHash_Instance *thi, BitLength outputBitLen,
        const BitSequence *customization, BitLength customBitLen)
{
    if (cSHAKE_Initialize(&thi->csi, outputBitLen, (const BitSequence*)"TupleHash", 9*8, customization, customBitLen) != 0)
        return 1;
    thi->outputBitLen = outputBitLen;
    return 0;
}

int TupleHash_Update(TupleHash_Instance *thi, const TupleElement *tuple, size_t numberOfElements)
{
    unsigned char encbuf[sizeof(BitLength)+1];

    while (numberOfElements-- != 0) {
        if ((tuple->inputBitLen & 7) != 0) /* Only full bytes are supported */
            return 1;
        if (cSHAKE_Update(&thi->csi, encbuf, left_encode(encbuf, tuple->inputBitLen)*8) != 0)
            return 1;
        if (cSHAKE_Update(&thi->csi, tuple->input, tuple->inputBitLen) != 0)
            return 1;
        ++tuple;
    }
    return 0;
}

int TupleHash_Final(TupleHash_Instance *thi, BitSequence * output)
{
    unsigned char encbuf[sizeof(BitLength)+1];

    if (cSHAKE_Update(&thi->csi, encbuf, right_encode(encbuf, thi->outputBitLen)*8) != 0)
        return 1;
    return cSHAKE_Final(&thi->csi, output);
}

int TupleHash_Squeeze(TupleHash_Instance *thi, BitSequence *output, BitLength outputBitLen)
{
    return cSHAKE_Squeeze(&thi->csi, output, outputBitLen);
}

int TupleHash( const TupleElement *tuple, size_t numberOfElements,
        BitSequence *output, BitLength outputBitLen, const BitSequence *customization, BitLength customBitLen)
{
    TupleHash_Instance thi;

    if (outputBitLen == 0)
        return 1;
    if (TupleHash_Initialize(&thi, outputBitLen, customization, customBitLen) != 0)
        return 1;
    if (TupleHash_Update(&thi, tuple, numberOfElements) != 0)
        return 1;
    return TupleHash_Final(&thi, output);
}

#undef  TupleHash_Initialize
#undef  TupleHash_Update
#undef  TupleHash_Final
#undef  TupleHash_Squeeze
#undef  TupleHash

/* ------------------------------------------------------------------------- */

#undef  JOIN0
#undef  JOIN

#undef  capacity
#undef  capacityInBytes
#undef  capacityInLanes
#undef  rate
#undef  rateInBytes
#undef  rateInLanes

#undef  cSHAKE_Initialize
#undef  cSHAKE_Update
#undef  cSHAKE_Final
#undef  cSHAKE_Squeeze
#undef  cSHAKE
