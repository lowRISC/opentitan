// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_RSA_RSA_PADDING_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_RSA_RSA_PADDING_H_

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
 * Encode the message with PKCS#1 v1.5 encoding (RFC 8017, section 9.2).
 *
 * The caller must ensure that `encoded_message_len` 32-bit words are allocated
 * in the output buffer.
 *
 * We encode the message in reversed byte-order from the RFC because OTBN
 * interprets the message as a fully little-endian integer.
 *
 * @param message_digest Message digest to encode.
 * @param encoded_message_len Intended encoded message length in 32-bit words.
 * @param[out] encoded_message Encoded message.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t rsa_padding_pkcs1v15_encode(
    const otcrypto_hash_digest_t message_digest, size_t encoded_message_len,
    uint32_t *encoded_message);

/**
 * Check if the PKCS#1 v1.5 encoded message represents the message.
 *
 * If the encoded message does not match the message, this function will return
 * an OK status and write `kHardenedBoolFalse` into the result buffer. The
 * caller should not interpret an OK status as a match between the encoded and
 * raw messages, since the status return value is reserved for operational or
 * logical error codes.
 *
 * Since PKCS#1 v1.5 padding is deterministic, we verify by re-encoding the
 * message and comparing the result.
 *
 * @param message_digest Message digest to verify.
 * @param encoded_message Encoded message.
 * @param encoded_message_len Encoded message length in 32-bit words.
 * @param[out] result True if the check passed.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t rsa_padding_pkcs1v15_verify(
    const otcrypto_hash_digest_t message_digest,
    const uint32_t *encoded_message, const size_t encoded_message_len,
    hardened_bool_t *result);

/**
 * Encode the message with PSS encoding (RFC 8017, section 9.1.1).
 *
 * The caller must ensure that `encoded_message_len` 32-bit words are allocated
 * in the output buffer.
 *
 * We encode the message in reversed byte-order from the RFC because OTBN
 * interprets the message as a fully little-endian integer.
 *
 * @param message_digest Message digest to encode.
 * @param salt Salt value.
 * @param salt_len Length of the salt in 32-bit words.
 * @param encoded_message_len Intended encoded message length in 32-bit words.
 * @param[out] encoded_message Encoded message.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t rsa_padding_pss_encode(const otcrypto_hash_digest_t message_digest,
                                const uint32_t *salt, size_t salt_len,
                                size_t encoded_message_len,
                                uint32_t *encoded_message);

/**
 * Check if the PSS-encoded message represents the message.
 *
 * From RFC 8017, section 9.1.2. Assumes that the salt length always matches
 * the digest length of the chosen hash function.
 *
 * If the encoded message does not match the message digest, this function will
 * return an OK status and write `kHardenedBoolFalse` into the result buffer.
 * The caller should not interpret an OK status as a match between the encoded
 * and raw messages, since the status return value is reserved for operational
 * or logical error codes.
 *
 * Note that this function expects the encoded message in reversed byte-order
 * compared to the RFC, since OTBN is little-endian.
 *
 * Warning: modifies the encoded message in-place during comparison
 * (specifically, reverses the byte-order).
 *
 * @param message_digest Message digest to verify.
 * @param encoded_message Encoded message.
 * @param encoded_message_len Encoded message length in 32-bit words.
 * @param[out] result True if the check passed.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t rsa_padding_pss_verify(const otcrypto_hash_digest_t message_digest,
                                uint32_t *encoded_message,
                                size_t encoded_message_len,
                                hardened_bool_t *result);

/**
 * Maximum message byte-length for OAEP padding.
 *
 * As per RFC 8017, the maximum message byte-length for OAEP is k - 2*hLen - 2,
 * where k is the size of the RSA modulus in bytes and hLen is the digest
 * length of the hash function used for padding. This function provides a
 * simple convenience interface so that callers can check that buffers for
 * decoded messages are long enough.
 *
 * Returns an error if the hash mode is not supported (i.e., a non-fixed-length
 * hash function).
 *
 * @param hash_mode Hash function to use for OAEP.
 * @param rsa_wordlen RSA modulus size in 32-bit words.
 * @param[out] max_message_bytelen Maximum length of message in bytes.
 * @return Result of the operation (OK or error).
 */
status_t rsa_padding_oaep_max_message_bytelen(
    const otcrypto_hash_mode_t hash_mode, size_t rsa_wordlen,
    size_t *max_message_bytelen);

/**
 * Encode the message with OAEP encoding (RFC 8017, section 7.1.1, steps 1-2).
 *
 * The caller must ensure that `encoded_message_len` 32-bit words are allocated
 * in the output buffer.
 *
 * The maximum byte-length of the message (as per the RFC) is k - 2*hLen - 2,
 * where k is the RSA size and hLen is the length of the hash digest. This
 * function will return an error if the message is too long.
 *
 * The hash function must be a fixed-length (SHA-2 or SHA-3) hash function. The
 * MGF will always be MGF1 with the same hash function.
 *
 * We encode the message in reversed byte-order from the RFC because OTBN
 * interprets the message as a fully little-endian integer.
 *
 * @param hash_mode Hash function to use.
 * @param message Message to encode.
 * @param message_bytelen Message length in bytes.
 * @param label Label for OAEP.
 * @param label_bytelen Label length in bytes.
 * @param encoded_message_len Intended encoded message length in 32-bit words.
 * @param[out] encoded_message Encoded message.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t rsa_padding_oaep_encode(const otcrypto_hash_mode_t hash_mode,
                                 const uint8_t *message, size_t message_bytelen,
                                 const uint8_t *label, size_t label_bytelen,
                                 size_t encoded_message_len,
                                 uint32_t *encoded_message);

/**
 * Decode the OAEP-encoded message (RFC 8017, section 7.1.2, step 3).
 *
 * The maximum byte-length of the message (as per the RFC) is k - 2*hLen - 2,
 * where k is the RSA size and hLen is the length of the hash digest. The
 * caller must ensure there are at least this many bytes available for
 * `message`; they can call `rsa_padding_oaep_max_message_bytelen` to get the
 * exact value for a given hash mode and RSA size.
 *
 * The hash function must be a fixed-length (SHA-2 or SHA-3) hash function. The
 * MGF will always be MGF1 with the same hash function.
 *
 * Note that this function expects the encoded message in reversed byte-order
 * compared to the RFC, since OTBN is little-endian.
 *
 * Warning: modifies the encoded message in-place during comparison
 * (specifically, reverses the byte-order).
 *
 * @param hash_mode Hash function to use.
 * @param label Label for OAEP.
 * @param label_bytelen Label length in bytes.
 * @param encoded_message Encoded message.
 * @param encoded_message_len Encoded message length in 32-bit words.
 * @param[out] message Decoded message.
 * @param[out] message_bytelen Length of the message in bytes.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t rsa_padding_oaep_decode(const otcrypto_hash_mode_t hash_mode,
                                 const uint8_t *label, size_t label_bytelen,
                                 uint32_t *encoded_message,
                                 size_t encoded_message_len, uint8_t *message,
                                 size_t *message_bytelen);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_RSA_RSA_PADDING_H_
