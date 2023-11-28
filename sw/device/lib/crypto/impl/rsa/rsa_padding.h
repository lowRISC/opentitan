// Copyright lowRISC contributors.
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
status_t rsa_padding_pkcs1v15_encode(const hash_digest_t *message_digest,
                                     size_t encoded_message_len,
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
status_t rsa_padding_pkcs1v15_verify(const hash_digest_t *message_digest,
                                     const uint32_t *encoded_message,
                                     const size_t encoded_message_len,
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
status_t rsa_padding_pss_encode(const hash_digest_t *message_digest,
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
status_t rsa_padding_pss_verify(const hash_digest_t *message_digest,
                                uint32_t *encoded_message,
                                size_t encoded_message_len,
                                hardened_bool_t *result);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_RSA_RSA_PADDING_H_
