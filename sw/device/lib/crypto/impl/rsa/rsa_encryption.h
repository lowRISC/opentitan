// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_RSA_RSA_ENCRYPTION_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_RSA_RSA_ENCRYPTION_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/crypto/impl/rsa/rsa_datatypes.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Starts encrypting a message with RSA-2048; returns immediately.
 *
 * The key exponent must be F4=65537; no other exponents are supported.  The
 * padding scheme is OAEP, and the mask generation function (MGF) is MGF1 with
 * the hash function indicated by `hash_mode` and a salt the same length as the
 * hash function output.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param public_key RSA public key.
 * @param hash_mode Hash function to use for message encoding.
 * @param message Message to encrypt.
 * @param message_bytelen Message length in bytes.
 * @param label Label for OAEP padding.
 * @param label_bytelen Length of label in bytes.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t rsa_encrypt_2048_start(const rsa_2048_public_key_t *public_key,
                                const otcrypto_hash_mode_t hash_mode,
                                const uint8_t *message, size_t message_bytelen,
                                const uint8_t *label, size_t label_bytelen);

/**
 * Waits for an RSA-2048 encryption to complete.
 *
 * Should be invoked only after a `rsa_encrypt_2048_start` call. Blocks until
 * OTBN is done processing.
 *
 * @param[out] ciphertext Encrypted message.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t rsa_encrypt_2048_finalize(rsa_2048_int_t *ciphertext);

/**
 * Start decrypting a message with RSA-2048; returns immediately.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param private_key RSA private key.
 * @param ciphertext Encrypted message.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t rsa_decrypt_2048_start(const rsa_2048_private_key_t *private_key,
                                const rsa_2048_int_t *ciphertext);

/**
 * Waits for an RSA decryption to complete.
 *
 * Should be invoked only after an `rsa_decrypt_{size}_start`, but works for
 * any RSA size. Blocks until OTBN is done processing, and then infers the size
 * from the OTBN application mode.
 *
 * The only supported padding mode is OAEP (see IETF RFC 8017, section 7.1.2).
 * Only fixed-length hash functions (i.e. the SHA-2 or SHA-3 families) are
 * supported. The mask generation function (MGF) is MGF1 with the hash function
 * indicated by `hash_mode`.
 *
 * The caller must ensure that enough space is allocated at `plaintext` to hold
 * the largest possible plaintext, which is (as described in IETF RFC 8017,
 * section 7.1.2):
 *   <length of modulus> - 2 * <length of hash function> - 2 bytes
 *
 * For example, if the hash function here is SHA-512 (64-byte digest), the
 * maximum plaintext byte-length would be:
 *   (2048 / 8) - 2 * 64 - 2 = 126 bytes
 *
 * This routine will not necessarily use all available bytes in the plaintext,
 * and will write the actual length of the plaintext into `plaintext_bytelen`.
 *
 * @param hash_mode Hash function to use for message decoding.
 * @param label Label for OAEP padding.
 * @param label_bytelen Length of label in bytes.
 * @param plaintext_max_bytelen Space allocated for the plaintext in bytes.
 * @param[out] plaintext Decrypted message.
 * @param[out] plaintext_bytelen Length of plaintext in bytes.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t rsa_decrypt_finalize(const otcrypto_hash_mode_t hash_mode,
                              const uint8_t *label, size_t label_bytelen,
                              size_t plaintext_max_bytelen, uint8_t *plaintext,
                              size_t *plaintext_bytelen);

/**
 * Starts encrypting a message with RSA-3072; returns immediately.
 *
 * The key exponent must be F4=65537; no other exponents are supported.  The
 * padding scheme is OAEP, and the mask generation function (MGF) is MGF1 with
 * the hash function indicated by `hash_mode` and a salt the same length as the
 * hash function output.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param public_key RSA public key.
 * @param hash_mode Hash function to use for message encoding.
 * @param message Message to encrypt.
 * @param message_bytelen Message length in bytes.
 * @param label Label for OAEP padding.
 * @param label_bytelen Length of label in bytes.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t rsa_encrypt_3072_start(const rsa_3072_public_key_t *public_key,
                                const otcrypto_hash_mode_t hash_mode,
                                const uint8_t *message, size_t message_bytelen,
                                const uint8_t *label, size_t label_bytelen);

/**
 * Waits for an RSA-3072 encryption to complete.
 *
 * Should be invoked only after a `rsa_encrypt_3072_start` call. Blocks until
 * OTBN is done processing.
 *
 * @param[out] ciphertext Encrypted message.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t rsa_encrypt_3072_finalize(rsa_3072_int_t *ciphertext);

/**
 * Start decrypting a message with RSA-3072; returns immediately.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param private_key RSA private key.
 * @param ciphertext Encrypted message.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t rsa_decrypt_3072_start(const rsa_3072_private_key_t *private_key,
                                const rsa_3072_int_t *ciphertext);

/**
 * Starts encrypting a message with RSA-4096; returns immediately.
 *
 * The key exponent must be F4=65537; no other exponents are supported.  The
 * padding scheme is OAEP, and the mask generation function (MGF) is MGF1 with
 * the hash function indicated by `hash_mode` and a salt the same length as the
 * hash function output.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param public_key RSA public key.
 * @param hash_mode Hash function to use for message encoding.
 * @param message Message to encrypt.
 * @param message_bytelen Message length in bytes.
 * @param label Label for OAEP padding.
 * @param label_bytelen Length of label in bytes.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t rsa_encrypt_4096_start(const rsa_4096_public_key_t *public_key,
                                const otcrypto_hash_mode_t hash_mode,
                                const uint8_t *message, size_t message_bytelen,
                                const uint8_t *label, size_t label_bytelen);

/**
 * Waits for an RSA-4096 encryption to complete.
 *
 * Should be invoked only after a `rsa_encrypt_4096_start` call. Blocks until
 * OTBN is done processing.
 *
 * @param[out] ciphertext Encrypted message.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t rsa_encrypt_4096_finalize(rsa_4096_int_t *ciphertext);

/**
 * Start decrypting a message with RSA-4096; returns immediately.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param private_key RSA private key.
 * @param ciphertext Encrypted message.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t rsa_decrypt_4096_start(const rsa_4096_private_key_t *private_key,
                                const rsa_4096_int_t *ciphertext);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_RSA_RSA_ENCRYPTION_H_
