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

#ifndef _SP800_185_h_
#define _SP800_185_h_

#include "config.h"
#ifdef XKCP_has_KeccakP1600

#include <stddef.h>
#include <stdint.h>
#include "align.h"
#include "KeccakSponge.h"
#include "Phases.h"

#ifndef _Keccak_BitTypes_
#define _Keccak_BitTypes_
typedef uint8_t BitSequence;

typedef size_t BitLength;
#endif

typedef struct {
    KeccakWidth1600_SpongeInstance  sponge;
    BitLength                       fixedOutputLength;
    unsigned int                    lastByteBitLen;
    BitSequence                     lastByteValue;
    int                             emptyNameCustom;
    KCP_Phases                      phase;
} cSHAKE_Instance;

/** cSHAKE128 function, as defined in NIST's Special Publication 800-185,
  * published December 2016.
  * @param  input           Pointer to the input message (X).
  * @param  inputBitLen     The length of the input message in bits.
  * @param  output          Pointer to the output buffer.
  * @param  outputBitLen    The desired number of output bits (L).
  * @param  name            Pointer to the function name string (N).
  * @param  nameBitLen      The length of the function name in bits.
  *                         Only full bytes are supported, length must be a multiple of 8.
  * @param  customization   Pointer to the customization string (S).
  * @param  customBitLen    The length of the customization string in bits.
  * @return 0 if successful, 1 otherwise.
  */
int cSHAKE128( const BitSequence *input, BitLength inputBitLen, BitSequence *output, BitLength outputBitLen, const BitSequence *name, BitLength nameBitLen, const BitSequence *customization, BitLength customBitLen );

/**
  * Function to initialize the cSHAKE128 instance used in sequential hashing mode.
  * @param  cskInstance     Pointer to the hash instance to be initialized.
  * @param  outputBitLen    The desired number of output bits (L).
  *                         or 0 for an arbitrarily-long output (XOF).
  * @param  name            Pointer to the function name string (N).
  * @param  nameBitLen      The length of the function name in bits.
  *                         Only full bytes are supported, length must be a multiple of 8.
  * @param  customization   Pointer to the customization string (S).
  * @param  customBitLen    The length of the customization string in bits.
  * @return 0 if successful, 1 otherwise.
  */
int cSHAKE128_Initialize(cSHAKE_Instance *cskInstance, BitLength outputBitLen, const BitSequence *name, BitLength nameBitLen, const BitSequence *customization, BitLength customBitLen);

/**
  * Function to give input data to be absorbed.
  * @param  cskInstance     Pointer to the hash instance initialized by cSHAKE128_Initialize().
  * @param  input           Pointer to the input data.
  * @param  inputBitLen     The number of input bits provided in the input data.
  *                         Only the last update call can input a partial byte, other calls must have a length multiple of 8.
  * @return 0 if successful, 1 otherwise.
  */
int cSHAKE128_Update(cSHAKE_Instance *cskInstance, const BitSequence *input, BitLength inputBitLen);

/**
  * Function to call after all input blocks have been input and to get
  * output bits if the length was specified when calling cSHAKE128_Initialize().
  * @param  cskInstance     Pointer to the hash instance initialized by cSHAKE128_Initialize().
  *                         If @a outputBitLen was not 0 in the call to cSHAKE128_Initialize(), the number of
  *                         output bits is equal to @a outputBitLen.
  *                         If @a outputBitLen was 0 in the call to cSHAKE128_Initialize(), the output bits
  *                         must be extracted using the cSHAKE128_Squeeze() function.
  * @param  output          Pointer to the buffer where to store the output data.
  * @return 0 if successful, 1 otherwise.
  */
int cSHAKE128_Final(cSHAKE_Instance *cskInstance, BitSequence *output);

 /**
  * Function to squeeze output data.
  * @param  cskInstance     Pointer to the hash instance initialized by cSHAKE128_Initialize().
  * @param  output          Pointer to the buffer where to store the output data.
  * @param  outputBitLen    The number of output bits desired.
  *                         Only the last squeeze call can output a partial byte, 
  *                         other calls must have a length multiple of 8.
  * @pre    cSHAKE128_Final() must have been already called.
  * @return 0 if successful, 1 otherwise.
  */
int cSHAKE128_Squeeze(cSHAKE_Instance *cskInstance, BitSequence *output, BitLength outputBitLen);

/* ------------------------------------------------------------------------- */

/** cSHAKE256 function, as defined in NIST's Special Publication 800-185,
  * published December 2016.
  * @param  input           Pointer to the input message (X).
  * @param  inputBitLen     The length of the input message in bits.
  * @param  output          Pointer to the output buffer.
  * @param  outputBitLen    The desired number of output bits (L).
  * @param  name            Pointer to the function name string (N).
  * @param  nameBitLen      The length of the function name in bits.
  *                         Only full bytes are supported, length must be a multiple of 8.
  * @param  customization   Pointer to the customization string (S).
  * @param  customBitLen    The length of the customization string in bits.
  * @return 0 if successful, 1 otherwise.
  */
int cSHAKE256( const BitSequence *input, BitLength inputBitLen, BitSequence *output, BitLength outputBitLen, const BitSequence *name, BitLength nameBitLen, const BitSequence *customization, BitLength customBitLen );

/**
  * Function to initialize the cSHAKE256 instance used in sequential hashing mode.
  * @param  cskInstance     Pointer to the hash instance to be initialized.
  * @param  outputBitLen    The desired number of output bits (L).
  *                         or 0 for an arbitrarily-long output (XOF).
  * @param  name            Pointer to the function name string (N).
  * @param  nameBitLen      The length of the function name in bits.
  *                         Only full bytes are supported, length must be a multiple of 8.
  * @param  customization   Pointer to the customization string (S).
  * @param  customBitLen    The length of the customization string in bits.
  * @return 0 if successful, 1 otherwise.
  */
int cSHAKE256_Initialize(cSHAKE_Instance *cskInstance, BitLength outputBitLen, const BitSequence *name, BitLength nameBitLen, const BitSequence *customization, BitLength customBitLen);

/**
  * Function to give input data to be absorbed.
  * @param  cskInstance     Pointer to the hash instance initialized by cSHAKE256_Initialize().
  * @param  input           Pointer to the input data.
  * @param  inputBitLen     The number of input bits provided in the input data.
  *                         Only the last update call can input a partial byte, other calls must have a length multiple of 8.
  * @return 0 if successful, 1 otherwise.
  */
int cSHAKE256_Update(cSHAKE_Instance *cskInstance, const BitSequence *input, BitLength inputBitLen);

/**
  * Function to call after all input blocks have been input and to get
  * output bits if the length was specified when calling cSHAKE256_Initialize().
  * @param  cskInstance     Pointer to the hash instance initialized by cSHAKE256_Initialize().
  *                         If @a outputBitLen was not 0 in the call to cSHAKE256_Initialize(), the number of
  *                         output bits is equal to @a outputBitLen.
  *                         If @a outputBitLen was 0 in the call to cSHAKE256_Initialize(), the output bits
  *                         must be extracted using the cSHAKE256_Squeeze() function.
  * @param  output          Pointer to the buffer where to store the output data.
  * @return 0 if successful, 1 otherwise.
  */
int cSHAKE256_Final(cSHAKE_Instance *cskInstance, BitSequence *output);

 /**
  * Function to squeeze output data.
  * @param  cskInstance     Pointer to the hash instance initialized by cSHAKE256_Initialize().
  * @param  output          Pointer to the buffer where to store the output data.
  * @param  outputBitLen    The number of output bits desired.
  *                         Only the last squeeze call can output a partial byte, 
  *                         other calls must have a length multiple of 8.
  * @pre    cSHAKE256_Final() must have been already called.
  * @return 0 if successful, 1 otherwise.
  */
int cSHAKE256_Squeeze(cSHAKE_Instance *cskInstance, BitSequence *output, BitLength outputBitLen);

/* ------------------------------------------------------------------------- */

typedef struct {
    cSHAKE_Instance csi;
    BitLength outputBitLen;
} KMAC_Instance;

/** KMAC128 function, as defined in NIST's Special Publication 800-185,
  * published December 2016.
  * @param  key             Pointer to the key (K).
  * @param  keyBitLen       The length of the key in bits.
  * @param  input           Pointer to the input message (X).
  * @param  inputBitLen     The length of the input message in bits.
  *                         Only full bytes are supported, length must be a multiple of 8.
  * @param  output          Pointer to the output buffer.
  * @param  outputBitLen    The desired number of output bits (L).
  * @param  customization   Pointer to the customization string (S).
  * @param  customBitLen    The length of the customization string in bits.
  * @return 0 if successful, 1 otherwise.
  */
int KMAC128(const BitSequence *key, BitLength keyBitLen, const BitSequence *input, BitLength inputBitLen,
        BitSequence *output, BitLength outputBitLen, const BitSequence *customization, BitLength customBitLen);

/**
  * Function to initialize the KMAC128 instance used in sequential MACing mode.
  * @param  kmInstance      Pointer to the instance to be initialized.
  * @param  key             Pointer to the key (K).
  * @param  keyBitLen       The length of the key in bits.
  * @param  outputBitLen    The desired number of output bits (L).
  *                         or 0 for an arbitrarily-long output (XOF).
  * @param  customization   Pointer to the customization string (S).
  * @param  customBitLen    The length of the customization string in bits.
  * @return 0 if successful, 1 otherwise.
  */
int KMAC128_Initialize(KMAC_Instance *kmkInstance, const BitSequence *key, BitLength keyBitLen, BitLength outputBitLen,
        const BitSequence *customization, BitLength customBitLen);

/**
  * Function to give input data to be MACed.
  * @param  kmInstance      Pointer to the instance initialized by KMAC128_Initialize().
  * @param  input           Pointer to the input data.
  * @param  inputBitLen     The number of input bits provided in the input data.
  *                         Only full bytes are supported, length must be a multiple of 8.
  * @return 0 if successful, 1 otherwise.
  */
int KMAC128_Update(KMAC_Instance *kmkInstance, const BitSequence *input, BitLength inputBitLen);

/**
  * Function to call after all input data have been input and to get
  * output bits if the length was specified when calling KMAC128_Initialize().
  * @param  kmInstance      Pointer to the instance initialized by KMAC128_Initialize().
  *                         If @a outputBitLen was not 0 in the call to KMAC128_Initialize(), the number of
  *                         output bits is equal to @a outputBitLen.
  *                         If @a outputBitLen was 0 in the call to KMAC128_Initialize(), the output bits
  *                         must be extracted using the KMAC128_Squeeze() function.
  * @param  output          Pointer to the buffer where to store the output data.
  * @return 0 if successful, 1 otherwise.
  */
int KMAC128_Final(KMAC_Instance *kmkInstance, BitSequence *output);

 /**
  * Function to squeeze output data.
  * @param  kmInstance      Pointer to the instance initialized by KMAC128_Initialize().
  * @param  output          Pointer to the buffer where to store the output data.
  * @param  outputBitLen    The number of output bits desired.
  *                         Only the last squeeze call can output a partial byte,
  *                         other calls must have a length multiple of 8.
  * @pre    KMAC128_Final() must have been already called.
  * @return 0 if successful, 1 otherwise.
  */
int KMAC128_Squeeze(KMAC_Instance *kmkInstance, BitSequence *output, BitLength outputBitLen);

/* ------------------------------------------------------------------------- */

/** KMAC256 function, as defined in NIST's Special Publication 800-185,
  * published December 2016.
  * @param  key             Pointer to the key (K).
  * @param  keyBitLen       The length of the key in bits.
  * @param  input           Pointer to the input message (X).
  * @param  inputBitLen     The length of the input message in bits.
  *                         Only full bytes are supported, length must be a multiple of 8.
  * @param  output          Pointer to the output buffer.
  * @param  outputBitLen    The desired number of output bits (L).
  * @param  customization   Pointer to the customization string (S).
  * @param  customBitLen    The length of the customization string in bits.
  * @return 0 if successful, 1 otherwise.
  */
int KMAC256(const BitSequence *key, BitLength keyBitLen, const BitSequence *input, BitLength inputBitLen,
        BitSequence *output, BitLength outputBitLen, const BitSequence *customization, BitLength customBitLen);

/**
  * Function to initialize the KMAC256 instance used in sequential MACing mode.
  * @param  kmInstance      Pointer to the instance to be initialized.
  * @param  key             Pointer to the key (K).
  * @param  keyBitLen       The length of the key in bits.
  * @param  outputBitLen    The desired number of output bits (L).
  *                         or 0 for an arbitrarily-long output (XOF).
  * @param  customization   Pointer to the customization string (S).
  * @param  customBitLen    The length of the customization string in bits.
  * @return 0 if successful, 1 otherwise.
  */
int KMAC256_Initialize(KMAC_Instance *kmkInstance, const BitSequence *key, BitLength keyBitLen, BitLength outputBitLen,
        const BitSequence *customization, BitLength customBitLen);

/**
  * Function to give input data to be MACed.
  * @param  kmInstance      Pointer to the instance initialized by KMAC256_Initialize().
  * @param  input           Pointer to the input data.
  * @param  inputBitLen     The number of input bits provided in the input data.
  *                         Only full bytes are supported, length must be a multiple of 8.
  * @return 0 if successful, 1 otherwise.
  */
int KMAC256_Update(KMAC_Instance *kmkInstance, const BitSequence *input, BitLength inputBitLen);

/**
  * Function to call after all input data have been input and to get
  * output bits if the length was specified when calling KMAC256_Initialize().
  * @param  kmInstance      Pointer to the instance initialized by KMAC256_Initialize().
  *                         If @a outputBitLen was not 0 in the call to KMAC256_Initialize(), the number of
  *                         output bits is equal to @a outputBitLen.
  *                         If @a outputBitLen was 0 in the call to KMAC256_Initialize(), the output bits
  *                         must be extracted using the KMAC256_Squeeze() function.
  * @param  output          Pointer to the buffer where to store the output data.
  * @return 0 if successful, 1 otherwise.
  */
int KMAC256_Final(KMAC_Instance *kmkInstance, BitSequence *output);

 /**
  * Function to squeeze output data.
  * @param  kmInstance      Pointer to the instance initialized by KMAC256_Initialize().
  * @param  output          Pointer to the buffer where to store the output data.
  * @param  outputBitLen    The number of output bits desired.
  *                         Only the last squeeze call can output a partial byte,
  *                         other calls must have a length multiple of 8.
  * @pre    KMAC256_Final() must have been already called.
  * @return 0 if successful, 1 otherwise.
  */
int KMAC256_Squeeze(KMAC_Instance *kmkInstance, BitSequence *output, BitLength outputBitLen);

/* ------------------------------------------------------------------------- */

typedef struct {
    KeccakWidth1600_SpongeInstance queueNode;
    KeccakWidth1600_SpongeInstance finalNode;
    size_t fixedOutputLength;
    size_t blockLen;
    size_t queueAbsorbedLen;
    size_t totalInputSize;
    KCP_Phases phase;
} ParallelHash_Instance;

/** Parallel hash function ParallelHash128, as defined in NIST's Special Publication 800-185,
  * published December 2016.
  * @param  input           Pointer to the input message (X).
  * @param  inputBitLen     The number of input bits provided in the input data.
  *                         Only full bytes are supported, length must be a multiple of 8.
  * @param  blockByteLen    Block size (B) in bytes, must be a power of 2.
  *                         The minimum value is 8 in this implementation.
  * @param  output          Pointer to the output buffer.
  * @param  outputBitLen    The desired number of output bits (L).
  * @param  customization   Pointer to the customization string (S).
  * @param  customBitLen    The length of the customization string in bits.
  * @return 0 if successful, 1 otherwise.
  */
int ParallelHash128( const BitSequence *input, BitLength inputBitLen, size_t blockByteLen,
        BitSequence *output, BitLength outputBitLen, const BitSequence *customization, BitLength customBitLen);

/**
  * Function to initialize the parallel hash function ParallelHash128 instance used in sequential hashing mode.
  * @param  ParallelHashInstance     Pointer to the hash instance to be initialized.
  * @param  blockByteLen    Block size (B) in bytes, must be a power of 2.
  *                         The minimum value is 8 in this implementation.
  * @param  outputBitLen    The desired number of output bits (L).
  *                         or 0 for an arbitrarily-long output (XOF).
  * @param  customization   Pointer to the customization string (S).
  * @param  customBitLen    The length of the customization string in bits.
  * @return 0 if successful, 1 otherwise.
  */
int ParallelHash128_Initialize(ParallelHash_Instance *ParallelHashInstance, size_t blockByteLen,
        BitLength outputBitLen, const BitSequence *customization, BitLength customBitLen);

/**
  * Function to give input data to be absorbed.
  * @param  ParallelHashInstance     Pointer to the hash instance initialized by ParallelHash128_Initialize().
  * @param  input           Pointer to the input data (X).
  * @param  inputBitLen     The number of input bits provided in the input data.
  *                         Only full bytes are supported, length must be a multiple of 8.
  * @return 0 if successful, 1 otherwise.
  */
int ParallelHash128_Update(ParallelHash_Instance *ParallelHashInstance, const BitSequence *input, BitLength inputBitLen);

/**
  * Function to call after all input blocks have been input and to get
  * output bits if the length was specified when calling ParallelHash128_Initialize().
  * @param  ParallelHashInstance     Pointer to the hash instance initialized by ParallelHash128_Initialize().
  * If @a outputBitLen was not 0 in the call to ParallelHash128_Initialize(), the number of
  *     output bits is equal to @a outputBitLen.
  * If @a outputBitLen was 0 in the call to ParallelHash128_Initialize(), the output bits
  *     must be extracted using the ParallelHash128_Squeeze() function.
  * @param  output          Pointer to the buffer where to store the output data.
  * @return 0 if successful, 1 otherwise.
  */
int ParallelHash128_Final(ParallelHash_Instance *ParallelHashInstance, BitSequence * output);

 /**
  * Function to squeeze output data.
  * @param  ParallelHashInstance    Pointer to the hash instance initialized by ParallelHash128_Initialize().
  * @param  output          Pointer to the buffer where to store the output data.
  * @param  outputBitLen    The number of output bits desired.
  *                         Only the last squeeze call can output a partial byte,
  *                         other calls must have a length multiple of 8.
  * @pre    ParallelHash128_Final() must have been already called.
  * @return 0 if successful, 1 otherwise.
  */
int ParallelHash128_Squeeze(ParallelHash_Instance *ParallelHashInstance, BitSequence *output, BitLength outputBitLen);

/* ------------------------------------------------------------------------- */

/** Parallel hash function ParallelHash256, as defined in NIST's Special Publication 800-185,
  * published December 2016.
  * @param  input           Pointer to the input message (X).
  * @param  inputBitLen     The number of input bits provided in the input data.
  *                         Only full bytes are supported, length must be a multiple of 8.
  * @param  blockByteLen    Block size (B) in bytes, must be a power of 2.
  *                         The minimum value is 8 in this implementation.
  * @param  output          Pointer to the output buffer.
  * @param  outputBitLen    The desired number of output bits (L).
  * @param  customization   Pointer to the customization string (S).
  * @param  customBitLen    The length of the customization string in bits.
  * @return 0 if successful, 1 otherwise.
  */
int ParallelHash256( const BitSequence *input, BitLength inputBitLen, size_t blockByteLen,
        BitSequence *output, BitLength outputBitLen, const BitSequence *customization, BitLength customBitLen);

/**
  * Function to initialize the parallel hash function ParallelHash256 instance used in sequential hashing mode.
  * @param  ParallelHashInstance     Pointer to the hash instance to be initialized.
  * @param  blockByteLen    Block size (B) in bytes, must be a power of 2.
  *                         The minimum value is 8 in this implementation.
  * @param  outputBitLen    The desired number of output bits (L).
  *                         or 0 for an arbitrarily-long output (XOF).
  * @param  customization   Pointer to the customization string (S).
  * @param  customBitLen    The length of the customization string in bits.
  * @return 0 if successful, 1 otherwise.
  */
int ParallelHash256_Initialize(ParallelHash_Instance *ParallelHashInstance, size_t blockByteLen,
        BitLength outputBitLen, const BitSequence *customization, BitLength customBitLen);

/**
  * Function to give input data to be absorbed.
  * @param  ParallelHashInstance     Pointer to the hash instance initialized by ParallelHash256_Initialize().
  * @param  input           Pointer to the input data (X).
  * @param  inputBitLen     The number of input bits provided in the input data.
  *                         Only full bytes are supported, length must be a multiple of 8.
  * @return 0 if successful, 1 otherwise.
  */
int ParallelHash256_Update(ParallelHash_Instance *ParallelHashInstance, const BitSequence *input, BitLength inputBitLen);

/**
  * Function to call after all input blocks have been input and to get
  * output bits if the length was specified when calling ParallelHash256_Initialize().
  * @param  ParallelHashInstance     Pointer to the hash instance initialized by ParallelHash256_Initialize().
  * If @a outputBitLen was not 0 in the call to ParallelHash256_Initialize(), the number of
  *     output bits is equal to @a outputBitLen.
  * If @a outputBitLen was 0 in the call to ParallelHash256_Initialize(), the output bits
  *     must be extracted using the ParallelHash256_Squeeze() function.
  * @param  output          Pointer to the buffer where to store the output data.
  * @return 0 if successful, 1 otherwise.
  */
int ParallelHash256_Final(ParallelHash_Instance *ParallelHashInstance, BitSequence * output);

 /**
  * Function to squeeze output data.
  * @param  ParallelHashInstance    Pointer to the hash instance initialized by ParallelHash256_Initialize().
  * @param  output          Pointer to the buffer where to store the output data.
  * @param  outputBitLen    The number of output bits desired.
  *                         Only the last squeeze call can output a partial byte,
  *                         other calls must have a length multiple of 8.
  * @pre    ParallelHash256_Final() must have been already called.
  * @return 0 if successful, 1 otherwise.
  */
int ParallelHash256_Squeeze(ParallelHash_Instance *ParallelHashInstance, BitSequence *output, BitLength outputBitLen);

/* ------------------------------------------------------------------------- */

typedef struct {
    cSHAKE_Instance csi;
    BitLength outputBitLen;
} TupleHash_Instance;

typedef struct {
    /** Pointer to the tuple element data (Xn). */
    const BitSequence *input;

    /** The number of input bits provided in this tuple element.
     *  Only full bytes are supported, length must be a multiple of 8.
     */
    BitLength inputBitLen;
} TupleElement;

/** Tuple hash function TupleHash128, as defined in NIST's Special Publication 800-185,
  * published December 2016.
  * @param  tuple            Pointer to an array of tuple elements (X).
  * @param  numberOfElements The number of tuple elements provided in the input data.
  * @param  output           Pointer to the output buffer.
  * @param  outputBitLen     The desired number of output bits (L).
  * @param  customization    Pointer to the customization string (S).
  * @param  customBitLen     The length of the customization string in bits.
  * @return 0 if successful, 1 otherwise.
  */
int TupleHash128( const TupleElement *tuple, size_t numberOfElements,
        BitSequence *output, BitLength outputBitLen, const BitSequence *customization, BitLength customBitLen);

/**
  * Function to initialize the Tuple hash function TupleHash128 instance used in sequential hashing mode.
  * @param  TupleHashInstance     Pointer to the hash instance to be initialized.
  * @param  outputBitLen    The desired number of output bits (L).
  *                         or 0 for an arbitrarily-long output (XOF).
  * @param  customization   Pointer to the customization string (S).
  * @param  customBitLen    The length of the customization string in bits.
  * @return 0 if successful, 1 otherwise.
  */
int TupleHash128_Initialize(TupleHash_Instance *TupleHashInstance, BitLength outputBitLen,
        const BitSequence *customization, BitLength customBitLen);

/**
  * Function to give input data to be absorbed.
  * @param  TupleHashInstance     Pointer to the hash instance initialized by TupleHash128_Initialize().
  * @param  tuple            Pointer to an array of tuple elements (X).
  * @param  numberOfElements The number of tuple elements provided in the input data.
  * @return 0 if successful, 1 otherwise.
  */
int TupleHash128_Update(TupleHash_Instance *TupleHashInstance, const TupleElement *tuple, size_t numberOfElements);

/**
  * Function to call after all input blocks have been input and to get
  * output bits if the length was specified when calling TupleHash128_Initialize().
  * @param  TupleHashInstance     Pointer to the hash instance initialized by TupleHash128_Initialize().
  * If @a outputBitLen was not 0 in the call to TupleHash128_Initialize(), the number of
  *     output bits is equal to @a outputBitLen.
  * If @a outputBitLen was 0 in the call to TupleHash128_Initialize(), the output bits
  *     must be extracted using the TupleHash128_Squeeze() function.
  * @param  output          Pointer to the buffer where to store the output data.
  * @return 0 if successful, 1 otherwise.
  */
int TupleHash128_Final(TupleHash_Instance *TupleHashInstance, BitSequence * output);

 /**
  * Function to squeeze output data.
  * @param  TupleHashInstance    Pointer to the hash instance initialized by TupleHash128_Initialize().
  * @param  output          Pointer to the buffer where to store the output data.
  * @param  outputBitLen    The number of output bits desired.
  *                         Only the last squeeze call can output a partial byte,
  *                         other calls must have a length multiple of 8.
  * @pre    TupleHash128_Final() must have been already called.
  * @return 0 if successful, 1 otherwise.
  */
int TupleHash128_Squeeze(TupleHash_Instance *TupleHashInstance, BitSequence *output, BitLength outputBitLen);

/* ------------------------------------------------------------------------- */

/** Tuple hash function TupleHash256, as defined in NIST's Special Publication 800-185,
  * published December 2016.
  * @param  tuple            Pointer to an array of tuple elements (X).
  * @param  numberOfElements The number of tuple elements provided in the input data.
  * @param  output           Pointer to the output buffer.
  * @param  outputBitLen     The desired number of output bits (L).
  * @param  customization    Pointer to the customization string (S).
  * @param  customBitLen     The length of the customization string in bits.
  * @return 0 if successful, 1 otherwise.
  */
int TupleHash256( const TupleElement *tuple, size_t numberOfElements,
        BitSequence *output, BitLength outputBitLen, const BitSequence *customization, BitLength customBitLen);

/**
  * Function to initialize the Tuple hash function TupleHash256 instance used in sequential hashing mode.
  * @param  TupleHashInstance     Pointer to the hash instance to be initialized.
  * @param  outputBitLen    The desired number of output bits (L).
  *                         or 0 for an arbitrarily-long output (XOF).
  * @param  customization   Pointer to the customization string (S).
  * @param  customBitLen    The length of the customization string in bits.
  * @return 0 if successful, 1 otherwise.
  */
int TupleHash256_Initialize(TupleHash_Instance *TupleHashInstance, BitLength outputBitLen,
        const BitSequence *customization, BitLength customBitLen);

/**
  * Function to give input data to be absorbed.
  * @param  TupleHashInstance     Pointer to the hash instance initialized by TupleHash256_Initialize().
  * @param  tuple            Pointer to an array of tuple elements (X).
  * @param  numberOfElements The number of tuple elements provided in the input data.
  * @return 0 if successful, 1 otherwise.
  */
int TupleHash256_Update(TupleHash_Instance *TupleHashInstance, const TupleElement *tuple, size_t numberOfElements);

/**
  * Function to call after all input blocks have been input and to get
  * output bits if the length was specified when calling TupleHash256_Initialize().
  * @param  TupleHashInstance     Pointer to the hash instance initialized by TupleHash256_Initialize().
  * If @a outputBitLen was not 0 in the call to TupleHash256_Initialize(), the number of
  *     output bits is equal to @a outputBitLen.
  * If @a outputBitLen was 0 in the call to TupleHash256_Initialize(), the output bits
  *     must be extracted using the TupleHash256_Squeeze() function.
  * @param  output          Pointer to the buffer where to store the output data.
  * @return 0 if successful, 1 otherwise.
  */
int TupleHash256_Final(TupleHash_Instance *TupleHashInstance, BitSequence * output);

 /**
  * Function to squeeze output data.
  * @param  TupleHashInstance    Pointer to the hash instance initialized by TupleHash256_Initialize().
  * @param  output          Pointer to the buffer where to store the output data.
  * @param  outputBitLen    The number of output bits desired.
  *                         Only the last squeeze call can output a partial byte,
  *                         other calls must have a length multiple of 8.
  * @pre    TupleHash256_Final() must have been already called.
  * @return 0 if successful, 1 otherwise.
  */
int TupleHash256_Squeeze(TupleHash_Instance *TupleHashInstance, BitSequence *output, BitLength outputBitLen);

#else
#error This requires an implementation of Keccak-p[1600]
#endif

#endif
