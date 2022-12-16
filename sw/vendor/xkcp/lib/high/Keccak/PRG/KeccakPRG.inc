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

#define JOIN0(a, b)                     a ## b
#define JOIN(a, b)                      JOIN0(a, b)

#define SpongePRG_Instance              JOIN(prefix, _SpongePRG_Instance)
#define SpongePRG_Initialize            JOIN(prefix, _SpongePRG_Initialize)
#define SpongePRG_Feed                  JOIN(prefix, _SpongePRG_Feed)
#define SpongePRG_Fetch                 JOIN(prefix, _SpongePRG_Fetch)
#define SpongePRG_Forget                JOIN(prefix, _SpongePRG_Forget)

#define DuplexInstance                  JOIN(prefix, _DuplexInstance)
#define DuplexInitialize                JOIN(prefix, _DuplexInitialize)
#define Duplexing                       JOIN(prefix, _Duplexing)
#define DuplexingFeedPartialInput       JOIN(prefix, _DuplexingFeedPartialInput)
#define DuplexingOverwriteWithZeroes    JOIN(prefix, _DuplexingOverwriteWithZeroes)
#define DuplexingGetFurtherOutput       JOIN(prefix, _DuplexingGetFurtherOutput)
#define DuplexGetInputIndex(duplex)     (duplex)->byteInputIndex
#define DuplexGetOutputIndex(duplex)    (duplex)->byteOutputIndex
#define DuplexSetOutputIndex(duplex, i) (duplex)->byteOutputIndex = (i)

int SpongePRG_Initialize(SpongePRG_Instance *instance, unsigned int capacity)
{
    unsigned int rate;
    unsigned int rhoInBytes;

    if (capacity > (SnP_width-10))
        return 1;

    rate = SnP_width - capacity;
    rhoInBytes = (rate-2)/8;

    if ( (rhoInBytes == 0) || (rhoInBytes >= SnP_width/8) )
        return 1;
    return DuplexInitialize(&instance->duplex, rate, capacity);
}

int SpongePRG_Feed(SpongePRG_Instance *instance, const unsigned char *input, unsigned int inputByteLen)
{
    unsigned int rhoInBytes = (instance->duplex.rate-2)/8;
    int error = 0;

    while( !error && (inputByteLen >= rhoInBytes - DuplexGetInputIndex(&instance->duplex))) {
        unsigned int localSize = rhoInBytes - DuplexGetInputIndex(&instance->duplex);
        error |= DuplexingFeedPartialInput(&instance->duplex, input, localSize);
        error |= Duplexing(&instance->duplex, 0, 0, 0, 0, 0x01);
        input += localSize;
        inputByteLen -= localSize;
    }
    if (!error)
        error = DuplexingFeedPartialInput(&instance->duplex, input, inputByteLen);
    DuplexSetOutputIndex(&instance->duplex, rhoInBytes);
    return error;
}

int SpongePRG_Fetch(SpongePRG_Instance *instance, unsigned char *output, unsigned int outputByteLen)
{
    unsigned int rhoInBytes = (instance->duplex.rate-2)/8;
    int error = 0;

    if (DuplexGetOutputIndex(&instance->duplex) < rhoInBytes) {
        unsigned int localSize = rhoInBytes - DuplexGetOutputIndex(&instance->duplex);
        localSize = (localSize <= outputByteLen) ? localSize : outputByteLen;
        error = DuplexingGetFurtherOutput(&instance->duplex, output, localSize);
        output += localSize;
        outputByteLen -= localSize;
    }

    while( !error && (outputByteLen > 0) ) {
        error = Duplexing(&instance->duplex, 0, 0, 0, 0, 0x01);
        if (!error) {
            unsigned int localSize = (rhoInBytes <= outputByteLen) ? rhoInBytes : outputByteLen;
            error = DuplexingGetFurtherOutput(&instance->duplex, output, localSize);
            output += localSize;
            outputByteLen -= localSize;
        }
    }
    return error;
}

int SpongePRG_Forget(SpongePRG_Instance *instance)
{
    unsigned int rhoInBytes = (instance->duplex.rate-2)/8;
    unsigned int capacity = SnP_width - instance->duplex.rate;
    int error;

    if ((rhoInBytes*8) < capacity)
        return 1;

    error = Duplexing(&instance->duplex, 0, 0, 0, 0, 0x01);
    if ( !error ) {
        error = DuplexingOverwriteWithZeroes(&instance->duplex, rhoInBytes);
        if ( !error )
            error = Duplexing(&instance->duplex, 0, 0, 0, 0, 0x01);
    }
    DuplexSetOutputIndex(&instance->duplex, rhoInBytes);
    return error;
}

#undef SpongePRG_Instance
#undef SpongePRG_Initialize
#undef SpongePRG_Feed
#undef SpongePRG_Fetch
#undef SpongePRG_Forget

#undef DuplexInstance
#undef DuplexInitialize
#undef Duplexing
#undef DuplexingFeedPartialInput
#undef DuplexingOverwriteWithZeroes
#undef DuplexingGetFurtherOutput
#undef DuplexGetInputIndex
#undef DuplexGetOutputIndex
#undef DuplexSetOutputIndex
