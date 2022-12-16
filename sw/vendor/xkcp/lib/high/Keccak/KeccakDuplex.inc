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

#define JOIN0(a, b)                     a ## b
#define JOIN(a, b)                      JOIN0(a, b)

#define DuplexInstance                  JOIN(prefix, _DuplexInstance)
#define DuplexInitialize                JOIN(prefix, _DuplexInitialize)
#define Duplexing                       JOIN(prefix, _Duplexing)
#define DuplexingFeedPartialInput       JOIN(prefix, _DuplexingFeedPartialInput)
#define DuplexingFeedZeroes             JOIN(prefix, _DuplexingFeedZeroes)
#define DuplexingOverwritePartialInput  JOIN(prefix, _DuplexingOverwritePartialInput)
#define DuplexingOverwriteWithZeroes    JOIN(prefix, _DuplexingOverwriteWithZeroes)
#define DuplexingGetFurtherOutput       JOIN(prefix, _DuplexingGetFurtherOutput)
#define DuplexingGetFurtherOutputAndAdd JOIN(prefix, _DuplexingGetFurtherOutputAndAdd)

#define SnP_stateSizeInBytes            JOIN(SnP, _stateSizeInBytes)
#define SnP_stateAlignment              JOIN(SnP, _stateAlignment)
#define SnP_StaticInitialize            JOIN(SnP, _StaticInitialize)
#define SnP_Initialize                  JOIN(SnP, _Initialize)
#define SnP_AddByte                     JOIN(SnP, _AddByte)
#define SnP_AddBytes                    JOIN(SnP, _AddBytes)
#define SnP_OverwriteBytes              JOIN(SnP, _OverwriteBytes)
#define SnP_OverwriteWithZeroes         JOIN(SnP, _OverwriteWithZeroes)
#define SnP_ExtractBytes                JOIN(SnP, _ExtractBytes)
#define SnP_ExtractAndAddBytes          JOIN(SnP, _ExtractAndAddBytes)

int DuplexInitialize(DuplexInstance *instance, unsigned int rate, unsigned int capacity)
{
    if (rate+capacity != SnP_width)
        return 1;
    if ((rate <= 2) || (rate > SnP_width))
        return 1;
    SnP_StaticInitialize();
    instance->rate = rate;
    SnP_Initialize(instance->state);
    instance->byteInputIndex = 0;
    instance->byteOutputIndex = (instance->rate+7)/8;
    return 0;
}

int Duplexing(DuplexInstance *instance, const unsigned char *sigmaBegin, unsigned int sigmaBeginByteLen, unsigned char *Z, unsigned int ZByteLen, unsigned char delimitedSigmaEnd)
{
    const unsigned int rho_max = instance->rate - 2;

    if (delimitedSigmaEnd == 0)
        return 1;
    if (sigmaBeginByteLen > rho_max/8)
        return 1;
    if ((instance->byteInputIndex+sigmaBeginByteLen)*8 > rho_max)
        return 1;
    if (rho_max - sigmaBeginByteLen*8 < 7) {
        unsigned int maxBitsInDelimitedSigmaEnd = rho_max - sigmaBeginByteLen*8;
        if (delimitedSigmaEnd >= (1 << (maxBitsInDelimitedSigmaEnd+1)))
            return 1;
    }
    if (ZByteLen > (instance->rate+7)/8)
        return 1; /* The output length must not be greater than the rate (rounded up to a byte) */

    SnP_AddBytes(instance->state, sigmaBegin, instance->byteInputIndex, sigmaBeginByteLen);
    #ifdef KeccakReference
    {
        unsigned char block[SnP_width/8];
        memcpy(block, sigmaBegin, sigmaBeginByteLen);
        block[sigmaBeginByteLen] = delimitedSigmaEnd;
        memset(block+sigmaBeginByteLen+1, 0, sizeof(block)-sigmaBeginByteLen-1);
        block[(instance->rate-1)/8] |= 1 << ((instance->rate-1) % 8);
        displayBytes(1, "Block to be absorbed (after padding)", block, (instance->rate+7)/8);
    }
    #endif

    /* Last few bits, whose delimiter coincides with first bit of padding */
    SnP_AddByte(instance->state, delimitedSigmaEnd, instance->byteInputIndex+sigmaBeginByteLen);
    /* Second bit of padding */
    SnP_AddByte(instance->state, (unsigned char)1 << ((instance->rate - 1)%8), (instance->rate - 1)/8);
    SnP_Permute(instance->state);
    SnP_ExtractBytes(instance->state, Z, 0, ZByteLen);

    if (ZByteLen*8 > instance->rate) {
        unsigned char mask = (unsigned char)(1 << (instance->rate % 8)) - 1;
        Z[ZByteLen-1] &= mask;
    }

    instance->byteInputIndex = 0;
    instance->byteOutputIndex = ZByteLen;

    return 0;
}

int DuplexingFeedPartialInput(DuplexInstance *instance, const unsigned char *input, unsigned int inputByteLen)
{
    const unsigned int rho_max = instance->rate - 2;

    if (inputByteLen > rho_max/8)
        return 1;
    if ((instance->byteInputIndex+inputByteLen)*8 > rho_max)
        return 1;

    SnP_AddBytes(instance->state, input, instance->byteInputIndex, inputByteLen);
    instance->byteInputIndex += inputByteLen;
    return 0;
}

int DuplexingFeedZeroes(DuplexInstance *instance, unsigned int inputByteLen)
{
    const unsigned int rho_max = instance->rate - 2;

    if (inputByteLen > rho_max/8)
        return 1;
    if ((instance->byteInputIndex+inputByteLen)*8 > rho_max)
        return 1;

    instance->byteInputIndex += inputByteLen;
    return 0;
}

int DuplexingOverwritePartialInput(DuplexInstance *instance, const unsigned char *input, unsigned int inputByteLen)
{
    const unsigned int rho_max = instance->rate - 2;

    if (inputByteLen > rho_max/8)
        return 1;
    if ((instance->byteInputIndex+inputByteLen)*8 > rho_max)
        return 1;

    SnP_OverwriteBytes(instance->state, input, instance->byteInputIndex, inputByteLen);
    instance->byteInputIndex += inputByteLen;
    return 0;
}

int DuplexingOverwriteWithZeroes(DuplexInstance *instance, unsigned int inputByteLen)
{
    const unsigned int rho_max = instance->rate - 2;

    if (inputByteLen > rho_max/8)
        return 1;
    if ((instance->byteInputIndex != 0) || (inputByteLen*8 > rho_max))
        return 1;

    SnP_OverwriteWithZeroes(instance->state, inputByteLen);
    instance->byteInputIndex = inputByteLen;

    return 0;
}

int DuplexingGetFurtherOutput(DuplexInstance *instance, unsigned char *output, unsigned int outputByteLen)
{
    if (outputByteLen > (instance->rate+7)/8 - instance->byteOutputIndex)
        return 1; /* The output length must not be greater than the rate (rounded up to a byte) */

    SnP_ExtractBytes(instance->state, output, instance->byteOutputIndex, outputByteLen);
    instance->byteOutputIndex += outputByteLen;
    if (instance->byteOutputIndex*8 > instance->rate) {
        unsigned char mask = (1 << (instance->rate % 8)) - 1;
        output[outputByteLen-1] &= mask;
    }
    return 0;
}

int DuplexingGetFurtherOutputAndAdd(DuplexInstance *instance, const unsigned char *input, unsigned char *output, unsigned int outputByteLen)
{
    if (outputByteLen > (instance->rate+7)/8 - instance->byteOutputIndex)
        return 1; /* The output length must not be greater than the rate (rounded up to a byte) */

    SnP_ExtractAndAddBytes(instance->state, input, output, instance->byteOutputIndex, outputByteLen);
    instance->byteOutputIndex += outputByteLen;
    if (instance->byteOutputIndex*8 > instance->rate) {
        unsigned char mask = (1 << (instance->rate % 8)) - 1;
        output[outputByteLen-1] &= mask;
    }
    return 0;
}

#undef DuplexInstance
#undef DuplexInitialize
#undef Duplexing
#undef DuplexingFeedPartialInput
#undef DuplexingFeedZeroes
#undef DuplexingOverwritePartialInput
#undef DuplexingOverwriteWithZeroes
#undef DuplexingGetFurtherOutput
#undef DuplexingGetFurtherOutputAndAdd
#undef SnP_stateSizeInBytes
#undef SnP_stateAlignment
#undef SnP_StaticInitialize
#undef SnP_Initialize
#undef SnP_AddByte
#undef SnP_AddBytes
#undef SnP_OverwriteBytes
#undef SnP_OverwriteWithZeroes
#undef SnP_ExtractBytes
#undef SnP_ExtractAndAddBytes
