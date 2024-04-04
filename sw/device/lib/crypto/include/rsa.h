// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_RSA_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_RSA_H_

#include "datatypes.h"

/**
 * @file
 * @brief RSA signature operations for the OpenTitan cryptography library.
 */

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Enum to define padding scheme for RSA signature data.
 *
 * Values are hardened.
 */
typedef enum otcrypto_rsa_padding {
  // Pads input data according to the PKCS#1 (v1.5) scheme.
  kOtcryptoRsaPaddingPkcs = 0x94e,
  // Pads input data according to the PKCS#1-PSS scheme. The mask generation
  // function is MGF1 with the same hash function as the input message
  // (supported SHA2 or SHA3 hash functions only).
  kOtcryptoRsaPaddingPss = 0x6b1,
} otcrypto_rsa_padding_t;

/**
 * Enum to define possible lengths of RSA (public) keys.
 *
 * Values are hardened.
 */
typedef enum otcrypto_rsa_size {
  // 2048-bit RSA.
  kOtcryptoRsaSize2048 = 0x5d1,
  // 3072-bit RSA.
  kOtcryptoRsaSize3072 = 0xc35,
  // 4096-bit RSA.
  kOtcryptoRsaSize4096 = 0x8da,
} otcrypto_rsa_size_t;

enum {
  /**
   * Number of bytes needed for RSA public keys.
   *
   * The exact representation is an implementation-specific detail and subject
   * to change. This is the length that the caller should set as `key_length`
   * and allocate for the `key` buffer in unblinded keys.
   */
  kOtcryptoRsa2048PublicKeyBytes = 260,
  kOtcryptoRsa3072PublicKeyBytes = 388,
  kOtcryptoRsa4096PublicKeyBytes = 516,
  /**
   * Number of bytes needed for RSA private keys.
   *
   * The exact representation is an implementation-specific detail and subject
   * to change. This is the length that the caller should set in `key_length`
   * for the blinded key configuration (NOT the blinded keyblob length).
   */
  kOtcryptoRsa2048PrivateKeyBytes = 256,
  kOtcryptoRsa3072PrivateKeyBytes = 384,
  kOtcryptoRsa4096PrivateKeyBytes = 512,
  /**
   * Number of bytes needed for RSA private keyblobs.
   *
   * The exact representation is an implementation-specific detail and subject
   * to change. This is the length that the caller should set in
   * `keyblob_length` and allocate for the `keyblob` buffer in blinded keys.
   */
  kOtcryptoRsa2048PrivateKeyblobBytes = 512,
  kOtcryptoRsa3072PrivateKeyblobBytes = 768,
  kOtcryptoRsa4096PrivateKeyblobBytes = 1024,
};

/**
 * Performs the RSA key generation.
 *
 * Computes RSA private key (d) and RSA public key exponent (e) and
 * modulus (n).
 *
 * The caller should allocate space for the public key and set the `key` and
 * `key_length` fields accordingly.
 *
 * The caller should fully populate the blinded key configuration and allocate
 * space for the keyblob, setting `config.key_length` and `keyblob_length`
 * accordingly.
 *
 * The value in the `checksum` field of key structs is not checked here and
 * will be populated by the key generation function.
 *
 * @param size RSA size parameter.
 * @param[out] public_key Pointer to public key struct.
 * @param[out] private_key Pointer to blinded private key struct.
 * @return Result of the RSA key generation.
 */
otcrypto_status_t otcrypto_rsa_keygen(otcrypto_rsa_size_t size,
                                      otcrypto_unblinded_key_t *public_key,
                                      otcrypto_blinded_key_t *private_key);

/**
 * Constructs an RSA public key from the modulus and public exponent.
 *
 * The caller should allocate space for the public key and set the `key` and
 * `key_length` fields accordingly.
 *
 * @param size RSA size parameter.
 * @param modulus RSA modulus (n).
 * @param exponent RSA public exponent (e).
 * @param[out] public_key Destination public key struct.
 * @return Result of the RSA key construction.
 */
otcrypto_status_t otcrypto_rsa_public_key_construct(
    otcrypto_rsa_size_t size, otcrypto_const_word32_buf_t modulus,
    uint32_t exponent, otcrypto_unblinded_key_t *public_key);

/**
 * Constructs an RSA private key from the modulus and public/private exponents.
 *
 * The caller should allocate space for the private key and set the `keyblob`,
 * `keyblob_length`, and `key_length` fields accordingly.
 *
 * @param size RSA size parameter.
 * @param modulus RSA modulus (n).
 * @param exponent RSA public exponent (e).
 * @param d_share0 First share of the RSA private exponent d.
 * @param d_share1 Second share of the RSA private exponent d.
 * @param[out] public_key Destination public key struct.
 * @return Result of the RSA key construction.
 */
otcrypto_status_t otcrypto_rsa_private_key_from_exponents(
    otcrypto_rsa_size_t size, otcrypto_const_word32_buf_t modulus, uint32_t e,
    otcrypto_const_word32_buf_t d_share0, otcrypto_const_word32_buf_t d_share1,
    otcrypto_blinded_key_t *private_key);

/**
 * Constructs an RSA keypair from the public key and one prime cofactor.
 *
 * The caller should allocate space for the private key and set the `keyblob`,
 * `keyblob_length`, and `key_length` fields accordingly. Similarly, the caller
 * should allocate space for the public key and set the `key` and `key_length`
 * fields.
 *
 * @param size RSA size parameter.
 * @param modulus RSA modulus (n).
 * @param exponent RSA public exponent (e).
 * @param cofactor_share0 First share of the prime cofactor (p or q).
 * @param cofactor_share1 Second share of the prime cofactor (p or q).
 * @param[out] public_key Destination public key struct.
 * @param[out] private_key Destination private key struct.
 * @return Result of the RSA key construction.
 */
otcrypto_status_t otcrypto_rsa_keypair_from_cofactor(
    otcrypto_rsa_size_t size, otcrypto_const_word32_buf_t modulus, uint32_t e,
    otcrypto_const_word32_buf_t cofactor_share0,
    otcrypto_const_word32_buf_t cofactor_share1,
    otcrypto_unblinded_key_t *public_key, otcrypto_blinded_key_t *private_key);

/**
 * Computes the digital signature on the input message data.
 *
 * The caller should allocate space for the `signature` buffer
 * and set the length of expected output in the `len` field of
 * `signature`. If the user-set length and the output length does not
 * match, an error message will be returned.
 *
 * @param private_key Pointer to blinded private key struct.
 * @param message_digest Message digest to be signed (pre-hashed).
 * @param padding_mode Padding scheme to be used for the data.
 * @param[out] signature Pointer to the generated signature struct.
 * @return The result of the RSA signature generation.
 */
otcrypto_status_t otcrypto_rsa_sign(const otcrypto_blinded_key_t *private_key,
                                    const otcrypto_hash_digest_t message_digest,
                                    otcrypto_rsa_padding_t padding_mode,
                                    otcrypto_word32_buf_t signature);

/**
 * Verifies the authenticity of the input signature.
 *
 * An "OK" status code does not mean that the signature passed verification;
 * the caller must check both the returned status and `verification_result`
 * before trusting the signature.
 *
 * @param public_key Pointer to public key struct.
 * @param message_digest Message digest to be verified (pre-hashed).
 * @param padding_mode Padding scheme to be used for the data.
 * @param signature Pointer to the input signature to be verified.
 * @param[out] verification_result Result of signature verification.
 * @return Result of the RSA verify operation.
 */
otcrypto_status_t otcrypto_rsa_verify(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_hash_digest_t message_digest,
    otcrypto_rsa_padding_t padding_mode, otcrypto_const_word32_buf_t signature,
    hardened_bool_t *verification_result);

/**
 * Encrypts a message with RSA.
 *
 * The only padding scheme available is OAEP, where the hash function is a
 * member of the SHA-2 or SHA-3 family and the mask generation function is
 * MGF1 with the same hash function.
 *
 * OAEP imposes strict limits on the length of the message (see IETF RFC 8017
 * for details). Specifically, the message is at most k - 2*hLen - 2 bytes
 * long, where k is the byte-length of the RSA modulus and hLen is the length
 * of the hash function digest. If the message is too long, this function will
 * return an error.
 *
 * The caller should allocate space for the `ciphertext` buffer and set the
 * length of expected output in the `len` field of `signature`. The ciphertext
 * is always the same length as the RSA modulus (so an RSA-2048 ciphertext is
 * always 2048 bits long). If the length does not match the private key mode,
 * this function returns an error.
 *
 * Note: RSA encryption is included for compatibility with legacy interfaces,
 * and is typically not recommended for modern applications because it is
 * slower and more fragile than other encryption methods. Consult an expert
 * before using RSA encryption.
 *
 * @param private_key Pointer to public key struct.
 * @param hash_mode Hash function to use for OAEP encoding.
 * @param message Message to encrypt.
 * @param label Label for OAEP encoding.
 * @param[out] ciphertext Buffer for the ciphertext.
 * @return The result of the RSA encryption operation.
 */
otcrypto_status_t otcrypto_rsa_encrypt(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_hash_mode_t hash_mode, otcrypto_const_byte_buf_t message,
    otcrypto_const_byte_buf_t label, otcrypto_word32_buf_t ciphertext);

/**
 * Decrypts a message with RSA.
 *
 * The only padding scheme available is OAEP, where the hash function is a
 * member of the SHA-2 or SHA-3 family and the mask generation function is
 * MGF1 with the same hash function.
 *
 * The caller should allocate space for the `plaintext` buffer and set the
 * allocated length in the `len` field. The length should be at least as long
 * as the maximum message length imposed by OAEP; that is, k - 2*hLen - 2 bytes
 * long, where k is the byte-length of the RSA modulus and hLen is the length
 * of the hash function digest. If the plaintext buffer is not long enough,
 * this function will return an error.
 *
 * Decryption recovers the original length of the plaintext buffer and will
 * return its value in `plaintext_bytelen`.
 *
 * Note: RSA encryption is included for compatibility with legacy interfaces,
 * and is typically not recommended for modern applications because it is
 * slower and more fragile than other encryption methods. Consult an expert
 * before using RSA encryption.
 *
 * @param private_key Pointer to blinded private key struct.
 * @param hash_mode Hash function to use for OAEP encoding.
 * @param ciphertext Ciphertext to decrypt.
 * @param label Label for OAEP encoding.
 * @param[out] plaintext Buffer for the decrypted message.
 * @param[out] plaintext_bytelen Recovered byte-length of plaintext.
 * @return Result of the RSA decryption operation.
 */
otcrypto_status_t otcrypto_rsa_decrypt(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_hash_mode_t hash_mode,
    otcrypto_const_word32_buf_t ciphertext, otcrypto_const_byte_buf_t label,
    otcrypto_byte_buf_t plaintext, size_t *plaintext_bytelen);
/**
 * Starts the asynchronous RSA key generation function.
 *
 * Initializes OTBN and starts the OTBN routine to compute the RSA
 * private key (d), RSA public key exponent (e) and modulus (n).
 *
 * @param size RSA size parameter.
 * @return Result of async RSA keygen start operation.
 */
otcrypto_status_t otcrypto_rsa_keygen_async_start(otcrypto_rsa_size_t size);

/**
 * Finalizes the asynchronous RSA key generation function.
 *
 * See `otcrypto_rsa_keygen` for details on the requirements for `public_key`
 * and `private_key`.
 *
 * @param[out] public_key Pointer to public key struct.
 * @param[out] private_key Pointer to blinded private key struct.
 * @return Result of asynchronous RSA keygen finalize operation.
 */
otcrypto_status_t otcrypto_rsa_keygen_async_finalize(
    otcrypto_unblinded_key_t *public_key, otcrypto_blinded_key_t *private_key);

/**
 * Starts constructing an RSA private key using a cofactor.
 *
 * See `otcrypto_rsa_keypair_from_cofactor` for the details
 * on the requirements for input buffers.
 *
 * @param size RSA size parameter.
 * @param modulus RSA modulus (n).
 * @param exponent RSA public exponent (e).
 * @param cofactor_share0 First share of the prime cofactor (p or q).
 * @param cofactor_share1 Second share of the prime cofactor (p or q).
 * @return Result of the RSA key construction.
 */
otcrypto_status_t otcrypto_rsa_keypair_from_cofactor_async_start(
    otcrypto_rsa_size_t size, otcrypto_const_word32_buf_t modulus, uint32_t e,
    otcrypto_const_word32_buf_t cofactor_share0,
    otcrypto_const_word32_buf_t cofactor_share1);

/**
 * Finalizes constructing an RSA private key using a cofactor.
 *
 * See `otcrypto_rsa_keypair_from_cofactor` for the details
 * on the requirements for output buffers.
 *
 * The public key returned from this function is recomputed; we recommend that
 * the caller compare it to the originally passed public key value to ensure
 * that everything went as expected. If the key is invalid in certain ways
 * (such as the modulus not being divisible by the key), then the modulus will
 * not match the original input.
 *
 * @param[out] public_key Destination public key struct.
 * @param[out] private_key Destination private key struct.
 * @return Result of the RSA key construction.
 */
otcrypto_status_t otcrypto_rsa_keypair_from_cofactor_async_finalize(
    otcrypto_unblinded_key_t *public_key, otcrypto_blinded_key_t *private_key);

/**
 * Starts the asynchronous digital signature generation function.
 *
 * Initializes OTBN and starts the OTBN routine to compute the digital
 * signature on the input message.
 *
 * @param private_key Pointer to blinded private key struct.
 * @param message_digest Message digest to be signed (pre-hashed).
 * @param padding_mode Padding scheme to be used for the data.
 * @return Result of async RSA sign start operation.
 */
otcrypto_status_t otcrypto_rsa_sign_async_start(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_hash_digest_t message_digest,
    otcrypto_rsa_padding_t padding_mode);

/**
 * Finalizes the asynchronous digital signature generation function.
 *
 * See `otcrypto_rsa_sign` for details on the requirements for `signature`.
 *
 * @param[out] signature Pointer to generated signature struct.
 * @return Result of async RSA sign finalize operation.
 */
otcrypto_status_t otcrypto_rsa_sign_async_finalize(
    otcrypto_word32_buf_t signature);

/**
 * Starts the asynchronous signature verification function.
 *
 * Initializes OTBN and starts the OTBN routine to recover the message
 * from the input signature.
 *
 * @param public_key Pointer to public key struct.
 * @param signature Pointer to the input signature to be verified.
 * @return Result of async RSA verify start operation.
 */
otcrypto_status_t otcrypto_rsa_verify_async_start(
    const otcrypto_unblinded_key_t *public_key,
    otcrypto_const_word32_buf_t signature);

/**
 * Finalizes the asynchronous signature verification function.
 *
 * An "OK" status code does not mean that the signature passed verification;
 * the caller must check both the returned status and `verification_result`
 * before trusting the signature.
 *
 * @param message_digest Message digest to be verified (pre-hashed).
 * @param padding_mode Padding scheme to be used for the data.
 * @param[out] verification_result Result of signature verification.
 * @return Result of async RSA verify finalize operation.
 */
otcrypto_status_t otcrypto_rsa_verify_async_finalize(
    const otcrypto_hash_digest_t message_digest,
    otcrypto_rsa_padding_t padding_mode, hardened_bool_t *verification_result);

/**
 * Starts the asynchronous encryption function.
 *
 * See `otcrypto_rsa_encrypt` for details on the length requirements for
 * `message`.
 *
 * @param private_key Pointer to public key struct.
 * @param hash_mode Hash function to use for OAEP encoding.
 * @param message Message to encrypt.
 * @param label Label for OAEP encoding.
 * @return The result of the RSA encryption start operation.
 */
otcrypto_status_t otcrypto_rsa_encrypt_async_start(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_hash_mode_t hash_mode, otcrypto_const_byte_buf_t message,
    otcrypto_const_byte_buf_t label);

/**
 * Finalizes the asynchronous encryption function.
 *
 * See `otcrypto_rsa_encrypt` for details on the length requirements for
 * `ciphertext`. Infers the RSA size from `ciphertext`'s length, and will
 * return an error if this does not match the RSA size for the current OTBN
 * data.
 *
 * @param[out] ciphertext Buffer for the ciphertext.
 * @return The result of the RSA encryption operation.
 */
otcrypto_status_t otcrypto_rsa_encrypt_async_finalize(
    otcrypto_word32_buf_t ciphertext);

/**
 * Starts the asynchronous decryption function.
 *
 * See `otcrypto_rsa_decrypt` for details on the length requirements for
 * `ciphertext`.
 *
 * @param private_key Pointer to blinded private key struct.
 * @param ciphertext Ciphertext to decrypt.
 * @return Result of the RSA decryption start operation.
 */
otcrypto_status_t otcrypto_rsa_decrypt_async_start(
    const otcrypto_blinded_key_t *private_key,
    otcrypto_const_word32_buf_t ciphertext);

/**
 * Finalizes the asynchronous decryption function.
 *
 * See `otcrypto_rsa_decrypt` for details on the requirements for `plaintext`
 * length and the way in which the actual length of the plaintext is returned.
 *
 * @param hash_mode Hash function to use for OAEP encoding.
 * @param label Label for OAEP encoding.
 * @param[out] plaintext Buffer for the decrypted message.
 * @param[out] plaintext_bytelen Recovered byte-length of plaintext.
 * @return Result of the RSA decryption finalize operation.
 */
otcrypto_status_t otcrypto_rsa_decrypt_async_finalize(
    const otcrypto_hash_mode_t hash_mode, otcrypto_const_byte_buf_t label,
    otcrypto_byte_buf_t plaintext, size_t *plaintext_bytelen);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_RSA_H_
