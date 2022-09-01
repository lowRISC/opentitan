// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_API_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_API_H_

/**
 * @brief OS-facing API for the OpenTitan cryptography library.
 *
 * NOTE: This API is a work in progress, and the code here only records the
 * current state. It will continue to change until the API design is finalized.
 */

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Enum to define padding scheme for RSA data.
 *
 * Values are hardened.
 */
typedef enum rsa_padding {
  // Pads input data according to the PKCS#1 (v1.5) scheme.
  kRsaPaddingPkcs = 0x9f44,
  // Pads input data according to the PKCS#1-PSS scheme.
  kRsaPaddingPss = 0x88cf,
} rsa_padding_t;

/**
 * Enum to define hash modes for RSA schemes.
 *
 * Aligning with existing hash modes. Values are hardened.
 */
typedef enum rsa_hash {
  // SHA2-256 hashing mode for RSA.
  kRsaHashSha256 = 0xed4b,
  // SHA2-384 hashing mode for RSA.
  kRsaHashSha384 = 0x5dd0,
  // SHA2-512 hashing mode for RSA.
  kRsaHashSha512 = 0x0bab,
  // SHA3-384 hashing mode for RSA.
  kRsaHashSha3_384 = 0x65b7,
} rsa_hash_t;

/**
 * Struct to handle the RSA private exponent and modulus.
 */
typedef struct rsa_private_key {
  // Unblinded key struct with RSA modulus.
  crypto_unblinded_key_t n;
  // Blinded key struct with RSA private exponent.
  crypto_blinded_key_t d;
} rsa_private_key_t;

/**
 * Enum to define possible lengths of RSA (public) keys.
 *
 * Values are hardened.
 */
typedef enum rsa_key_size {
  // 2048-bit RSA key.
  kRsaKeySize2048 = 0xa74d,
  // 3072-bit RSA key.
  kRsaKeySize3072 = 0x7fc6,
  // 4096-bit RSA key.
  kRsaKeySize4096 = 0xf07a,
} rsa_key_size_t;

/**
 * Struct to handle the RSA public exponent and modulus.
 */
typedef struct rsa_public_key {
  // Unblinded key struct with RSA modulus.
  crypto_unblinded_key_t n;
  // Blinded key struct with RSA public exponent.
  crypto_unblinded_key_t e;
} rsa_public_key_t;

/**
 * Enum to define the supported KDF constructions.
 *
 * Values are hardened.
 */
typedef enum kdf_type {
  // KDF construction with HMAC as a PRF.
  kKdfTypeHmac = 0xfa3b,
  // KDF construction with KMAC as a PRF.
  kKdfTypeKmac = 0x0f47,
} kdf_type_t;

/**
 * DRBG state.
 *
 * Representation is internal to the drbg implementation; initialize
 * with #otcrypto_drbg_instantiate or
 * #otcrypto_drbg_manual_instantiate.
 *
 * Note: The drbg_state_t struct along with V and K, should include:
 * drbg_entropy_mode: To indicate the entropy mode used. Also used to
 * disallow mixing of auto entropy and manual entropy DRBG operations.
 * reseed_counter: To indicate the number of requests for pseudorandom
 * bits since instantiation or reseeding.
 * security_strength: To indicate security strength of the DRBG
 * instantiation.
 * prediction_resistance_flag: To indicate if prediction resistance is
 * required.
 * drbg_mechanism: To indicate if CTR_DRBG or HMAC_DRBG is used for
 * the DRBG instantiation.
 */
typedef struct drbg_state drbg_state_t;

/**
 * Performs the RSA key generation.
 *
 * Computes RSA private key (d) and RSA public key exponent (e) and
 * modulus (n).
 *
 * @param required_key_len Requested key length
 * @param rsa_public_key Pointer to RSA public exponent struct
 * @param rsa_private_key Pointer to RSA private exponent struct
 * @return Result of the RSA key generation
 */
crypto_status_t otcrypto_rsa_keygen(rsa_key_size_t required_key_len,
                                    rsa_public_key_t *rsa_public_key,
                                    rsa_private_key_t *rsa_private_key);

/**
 * Computes the digital signature on the input message data.
 *
 * The caller should allocate space for the `signature` buffer,
 * (expected length same as modulus length from `rsa_private_key`),
 * and set the length of expected output in the `len` field of
 * `signature`. If the user-set length and the output length does not
 * match, an error message will be returned.
 *
 * @param rsa_private_key Pointer to RSA private exponent struct
 * @param input_message Input message to be signed
 * @param padding_mode Padding scheme to be used for the data
 * @param hash_mode Hashing scheme to be used for the signature scheme
 * @param signature Pointer to generated signature struct
 * @return The result of the RSA sign generation
 */
crypto_status_t otcrypto_rsa_sign(const rsa_private_key_t *rsa_private_key,
                                  crypto_const_uint8_buf_t input_message,
                                  rsa_padding_t padding_mode,
                                  rsa_hash_t hash_mode,
                                  crypto_uint8_buf_t *signature);

/**
 * Verifies the authenticity of the input signature.
 *
 * The generated signature is compared against the input signature and
 * PASS / FAIL is returned.
 *
 * @param rsa_public_key Pointer to RSA public exponent struct
 * @param input_message Input message to be signed for verification
 * @param padding_mode Padding scheme to be used for the data
 * @param hash_mode Hashing scheme to be used for the signature scheme
 * @param signature Pointer to the input signature to be verified
 * @param verification_result Returns the result of signature
 * verification (Pass/Fail)
 * @return The status of the RSA verify operation
 */
crypto_status_t otcrypto_rsa_verify(const rsa_public_key_t *rsa_public_key,
                                    crypto_const_uint8_buf_t input_message,
                                    rsa_padding_t padding_mode,
                                    rsa_hash_t hash_mode,
                                    crypto_const_uint8_buf_t signature,
                                    verification_status_t *verification_result);

/**
 * Starts the asynchronous RSA key generation function.
 *
 * Initializes OTBN and starts the OTBN routine to compute the RSA
 * private key (d), RSA public key exponent (e) and modulus (n).
 *
 * Returns `kCryptoStatusOK` if the operation was successfully
 * started, or`kCryptoStatusInternalError` if the operation cannot be
 * started.
 *
 * @param required_key_len Requested key length
 * @return Result of async RSA keygen start operation
 */
crypto_status_t otcrypto_rsa_keygen_async_start(
    rsa_key_size_t required_key_len);

/**
 * Finalizes the asynchronous RSA key generation function.
 *
 * Returns `kCryptoStatusOK` and copies the RSA private key (d), RSA
 * public key exponent (e) and modulus (n) if the OTBN status is done,
 * or `kCryptoStatusAsyncIncomplete` if the OTBN is busy or
 * `kCryptoStatusInternalError` if there is an error.
 *
 * @param rsa_public_key Pointer to RSA public exponent struct
 * @param rsa_private_key Pointer to RSA private exponent struct
 * @return Result of asynchronous RSA keygen finalize
 * operation
 */
crypto_status_t otcrypto_rsa_keygen_async_finalize(
    rsa_public_key_t *rsa_public_key, rsa_private_key_t *rsa_private_key);

/**
 * Starts the asynchronous digital signature generation function.
 *
 * Initializes OTBN and starts the OTBN routine to compute the digital
 * signature on the input message.
 *
 * Returns `kCryptoStatusOK` if the operation was successfully
 * started, or`kCryptoStatusInternalError` if the operation cannot be
 * started.
 *
 * @param rsa_private_key Pointer to RSA private exponent struct
 * @param input_message Input message to be signed
 * @param padding_mode Padding scheme to be used for the data
 * @param hash_mode Hashing scheme to be used for the signature scheme
 * @return Result of async RSA sign start operation
 */
crypto_status_t otcrypto_rsa_sign_async_start(
    const rsa_private_key_t *rsa_private_key,
    crypto_const_uint8_buf_t input_message, rsa_padding_t padding_mode,
    rsa_hash_t hash_mode);

/**
 * Finalizes the asynchronous digital signature generation function.
 *
 * Returns `kCryptoStatusOK` and copies the signature if the OTBN
 * status is done, or `kCryptoStatusAsyncIncomplete` if the OTBN is
 * busy or `kCryptoStatusInternalError` if there is an error.
 *
 * The caller should allocate space for the `signature` buffer,
 * (expected length same as modulus length from `rsa_private_key`),
 * and set the length of expected output in the `len` field of
 * `signature`. If the user-set length and the output length does not
 * match, an error message will be returned.
 *
 * @param signature Pointer to generated signature struct
 * @return Result of async RSA sign finalize operation
 */
crypto_status_t otcrypto_rsa_sign_async_finalize(crypto_uint8_buf_t *signature);

/**
 * Starts the asynchronous signature verification function.
 *
 * Initializes OTBN and starts the OTBN routine to recover the message
 * from the input signature.
 *
 * @param rsa_public_key Pointer to RSA public exponent struct
 * @param signature Pointer to the input signature to be verified
 * @return Result of async RSA verify start operation
 */
crypto_status_t otcrypto_rsa_verify_async_start(
    const rsa_public_key_t *rsa_public_key, crypto_const_uint8_buf_t signature);

/**
 * Finalizes the asynchronous signature verification function.
 *
 * Returns `kCryptoStatusOK` and populates the `verification result`
 * if the OTBN status is done, or `kCryptoStatusAsyncIncomplete` if
 * OTBN is busy or `kCryptoStatusInternalError` if there is an error.
 * The (hash of) recovered message is compared against the input
 * message and a PASS or FAIL is returned.
 *
 * @param input_message Input message to be signed for verification
 * @param padding_mode Padding scheme to be used for the data
 * @param hash_mode Hashing scheme to be used for the signature scheme
 * @param verification_result Returns the result of verification
 * @return Result of async RSA verify finalize
 * operation
 */
crypto_status_t otcrypto_rsa_verify_async_finalize(
    crypto_const_uint8_buf_t input_message, rsa_padding_t padding_mode,
    rsa_hash_t hash_mode, verification_status_t *verification_result);

/**
 * Instantiates the DRBG system.
 *
 * Initializes the DRBG and the context for DRBG. Gets the required
 * entropy input automatically from the entropy source.
 *
 * @param drbg_state Pointer to the DRBG working state
 * @param nonce Pointer to the nonce bit-string
 * @param perso_string Pointer to personalization bitstring
 * @return Result of the DRBG instantiate operation
 */
crypto_status_t otcrypto_drbg_instantiate(drbg_state_t *drbg_state,
                                          crypto_uint8_buf_t nonce,
                                          crypto_uint8_buf_t perso_string);

/**
 * Reseeds the DRBG with fresh entropy.
 *
 * Reseeds the DRBG with fresh entropy that is automatically fetched
 * from the entropy source and updates the working state parameters.
 *
 * @param drbg_state Pointer to the DRBG working state
 * @param additional_input Pointer to the additional input for DRBG
 * @return Result of the DRBG reseed operation
 */
crypto_status_t otcrypto_drbg_reseed(drbg_state_t *drbg_state,
                                     crypto_uint8_buf_t additional_input);

/**
 * Instantiates the DRBG system.
 *
 * Initializes DRBG and the DRBG context. Gets the required entropy
 * input from the user through the `entropy` parameter.
 *
 * @param drbg_state Pointer to the DRBG working state
 * @param entropy Pointer to the user defined entropy value
 * @param nonce Pointer to the nonce bit-string
 * @param personalization_string Pointer to personalization bitstring
 * @return Result of the DRBG manual instantiation
 */
crypto_status_t otcrypto_drbg_manual_instantiate(
    drbg_state_t *drbg_state, crypto_uint8_buf_t entropy,
    crypto_uint8_buf_t nonce, crypto_uint8_buf_t perso_string);

/**
 * Reseeds the DRBG with fresh entropy.
 *
 * Reseeds the DRBG with entropy input from the user through `entropy`
 * parameter and updates the working state parameters.
 *
 * @param drbg_state Pointer to the DRBG working state
 * @param entropy Pointer to the user defined entropy value
 * @param additional_input Pointer to the additional input for DRBG
 * @return Result of the manual DRBG reseed operation
 */
crypto_status_t otcrypto_drbg_manual_reseed(
    drbg_state_t *drbg_state, crypto_uint8_buf_t entropy,
    crypto_uint8_buf_t additional_input);

/**
 * DRBG function for generating random bits.
 *
 * Used to generate pseudo random bits after DRBG instantiation or
 * DRBG reseeding.
 *
 * The caller should allocate space for the `drbg_output` buffer,
 * (of length `output_len`), and set the length of expected
 * output in the `len` field of `drbg_output`. If the user-set length
 * and the output length does not match, an error message will be
 * returned.
 *
 * @param drbg_state Pointer to the DRBG working state
 * @param additional_input Pointer to the additional data
 * @param output_len Required len of pseudorandom output, in bytes
 * @param drbg_output Pointer to the generated pseudo random bits
 * @return Result of the DRBG generate operation
 */
crypto_status_t otcrypto_drbg_generate(drbg_state_t *drbg_state,
                                       crypto_uint8_buf_t additional_input,
                                       size_t output_len,
                                       crypto_uint8_buf_t *drbg_output);

/**
 * Uninstantiates DRBG and clears the context.
 *
 * @param drbg_state Pointer to the DRBG working state
 * @return Result of the DRBG uninstantiate operation
 */
crypto_status_t otcrypto_drbg_uninstantiate(drbg_state_t *drbg_state);

/**
 * Performs the key derivation function in counter mode.
 *
 * The required PRF engine for the KDF function is selected using the
 * `kdf_mode` parameter.
 *
 * @param key_derivation_key Pointer to the blinded key derivation key
 * @param kdf_mode Required KDF mode, with HMAC or KMAC as a PRF
 * @param key_mode Crypto mode for which the derived key is intended
 * @param required_bit_len Required length of the derived key in bits
 * @param keying_material Pointer to the blinded keying material
 * @return Result of the key derivation operation
 */
crypto_status_t otcrypto_kdf_ctr(const crypto_blinded_key_t key_derivation_key,
                                 kdf_type_t kdf_mode, key_mode_t key_mode,
                                 size_t required_bit_len,
                                 crypto_blinded_key_t keying_material);

/**
 * Builds an unblinded key struct from a user (plain) key.
 *
 * @param plain_key Pointer to the user defined plain key
 * @param key_mode Crypto mode for which the key usage is intended
 * @param unblinded_key Generated unblinded key struct
 * @return Result of the build unblinded key operation
 */
crypto_status_t otcrypto_build_unblinded_key(
    crypto_const_uint8_buf_t plain_key, key_mode_t key_mode,
    crypto_unblinded_key_t unblinded_key);

/**
 * Builds a blinded key struct from a plain key.
 *
 * This API takes as input a plain key from the user and masks
 * it using an implantation specific masking with ‘n’ shares and
 * generates a blinded key struct as output.
 *
 * @param plain_key Pointer to the user defined plain key
 * @param key_mode Crypto mode for which the key usage is intended
 * @param blinded_key Generated blinded key struct
 * @return Result of the build blinded key operation
 */
crypto_status_t otcrypto_build_blinded_key(crypto_const_uint8_buf_t plain_key,
                                           key_mode_t key_mode,
                                           crypto_blinded_key_t blinded_key);

/**
 * Exports the blinded key struct to an unblinded key struct.
 *
 * This API takes as input a blinded key masked with ‘n’ shares, and
 * removes the masking and generates an unblinded key struct as output.
 *
 * @param blinded_key Blinded key struct to be unmasked
 * @param unblinded_key Generated unblinded key struct
 * @return Result of the blinded key export operation
 */
crypto_status_t otcrypto_blinded_to_unblinded_key(
    const crypto_blinded_key_t blinded_key,
    crypto_unblinded_key_t unblinded_key);

/**
 * Build a blinded key struct from an unblinded key struct.
 *
 * @param unblinded_key Blinded key struct to be unmasked
 * @param blinded_key Generated (unmasked) unblinded key struct
 * @return Result of unblinded key export operation
 */
crypto_status_t otcrypto_unblinded_to_blinded_key(
    const crypto_unblinded_key unblinded_key, crypto_blinded_key_t blinded_key);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_API_H_
