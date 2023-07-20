// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_KMAC_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_KMAC_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/crypto/impl/status.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * The exposed costants to caller functions.
 */
enum {
  // The total size of prefix registers (in bytes), after removing len encodings
  kKmacPrefixMaxSize = 40,
};

/**
 * Simplified key struct to pass blinded key internally.
 */
typedef struct kmac_blinded_key {
  uint32_t *share0;
  uint32_t *share1;
  // The length of single share (in bytes)
  size_t len;
} kmac_blinded_key_t;

/**
 * Check whether given key length is valid for KMAC.

 * @param key_len Key length as input.
 * @return Return OTCRYPTO_OK if valid and otherwise an error.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_key_length_check(size_t key_len);

/**
 * Set the "global" config of HWIP
 *
 * For the moment, we have a number of configuation options needs to be
 * configured at session level. This functions serves as a temporary
 * solution by setting default values to this configuration.
 * TODO: Define config struct and pass it as argument.
 * TODO: see #14832
 *
 * Warning: This function sets `entropy_ready`, which triggers kmac_entropy's
 * FSM to jump to next step. Therefore, the caller of this function should make
 * sure that entropy is configured properly beforehand.
 *
 * It enforces the following as the default configuration:
 * It touches the following fields of CSRs:
 *   CFG register:
 *     endianness, entropy_mode, fast_process, msg_mask, ent_ready,
 * err_processed, en_unsup_mode EDN refresh settings: hash threshold refresh
 * counter entropy seed -> ignore? INTR_ENABLE: all disabled
 *
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_hwip_default_configure(void);

/**
 * Compute SHA-3-224 in one-shot.
 *
 * The caller must ensure that there is at least 224 bits = 28 bytes of space
 * available at the location pointed to by `digest`.
 *
 * @param message The input message.
 * @param message_len The input message length in bytes.
 * @param[out] digest Output buffer for the result.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_sha3_224(const uint8_t *message, size_t message_len,
                       uint8_t *digest);

/**
 * Compute SHA-3-256 in one-shot.
 *
 * The caller must ensure that there is at least 256 bits = 32 bytes of space
 * available at the location pointed to by `digest`.
 *
 * @param message The input message.
 * @param message_len The input message length in bytes.
 * @param[out] digest Output buffer for the result.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_sha3_256(const uint8_t *message, size_t message_len,
                       uint8_t *digest);

/**
 * Compute SHA-3-384 in one-shot.
 *
 * The caller must ensure that there is at least 384 bits = 48 bytes of space
 * available at the location pointed to by `digest`.
 *
 * @param message The input message.
 * @param message_len The input message length in bytes.
 * @param[out] digest Output buffer for the result.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_sha3_384(const uint8_t *message, size_t message_len,
                       uint8_t *digest);

/**
 * Compute SHA-3-512 in one-shot.
 *
 * The caller must ensure that there is at least 512 bits = 64 bytes of space
 * available at the location pointed to by `digest`.
 *
 * @param message The input message.
 * @param message_len The input message length in bytes.
 * @param[out] digest Output buffer for the result.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_sha3_512(const uint8_t *message, size_t message_len,
                       uint8_t *digest);

/**
 * Compute SHAKE-128 in one-shot.
 *
 * The caller must ensure that `digest_len` bytes are allocated at the location
 * pointed to by `digest`.
 *
 * @param message The input message.
 * @param message_len The input message length in bytes.
 * @param[out] digest Output buffer for the result.
 * @param digest_len Requested digest length in bytes.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_shake_128(const uint8_t *message, size_t message_len,
                        uint8_t *digest, size_t digest_len);

/**
 * Compute SHAKE-256 in one-shot.
 *
 * The caller must ensure that `digest_len` bytes are allocated at the location
 * pointed to by `digest`.
 *
 * @param message The input message.
 * @param message_len The input message length in bytes.
 * @param[out] digest Output buffer for the result.
 * @param digest_len Requested digest length in bytes.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_shake_256(const uint8_t *message, size_t message_len,
                        uint8_t *digest, size_t digest_len);

/**
 * Compute CSHAKE-128 in one-shot.
 *
 * The caller must ensure that `digest_len` bytes are allocated at the location
 * pointed to by `digest`.
 *
 * @param message The input message.
 * @param message_len The input message length in bytes.
 * @param func_name The function name.
 * @param func_name_len The function name length in bytes.
 * @param cust_str The customization string.
 * @param cust_str_len The customization string length in bytes.
 * @param[out] digest Output buffer for the result.
 * @param digest_len Requested digest length in bytes.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_cshake_128(const uint8_t *message, size_t message_len,
                         const unsigned char *func_name, size_t func_name_len,
                         const unsigned char *cust_str, size_t cust_str_len,
                         uint8_t *digest, size_t digest_len);

/**
 * Compute CSHAKE-256 in one-shot.
 *
 * The caller must ensure that `digest_len` bytes are allocated at the location
 * pointed to by `digest`.
 *
 * @param message The input message.
 * @param message_len The input message length in bytes.
 * @param func_name The function name.
 * @param func_name_len The function name length in bytes.
 * @param cust_str The customization string.
 * @param cust_str_len The customization string length in bytes.
 * @param[out] digest Output buffer for the result.
 * @param digest_len Requested digest length in bytes.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_cshake_256(const uint8_t *message, size_t message_len,
                         const unsigned char *func_name, size_t func_name_len,
                         const unsigned char *cust_str, size_t cust_str_len,
                         uint8_t *digest, size_t digest_len);

/**
 * Compute KMAC-128 in one-shot.
 *
 * The caller must ensure that `digest_len` bytes are allocated at the location
 * pointed to by `digest`.
 *
 * @param message The input message.
 * @param message_len The input message length in bytes.
 * @param cust_str The customization string.
 * @param cust_str_len The customization string length in bytes.
 * @param[out] digest Output buffer for the result.
 * @param digest_len Requested digest length in bytes.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_kmac_128(kmac_blinded_key_t *key, const uint8_t *message,
                       size_t message_len, const unsigned char *cust_str,
                       size_t cust_str_len, uint8_t *digest, size_t digest_len);

/**
 * Compute KMAC-256 in one-shot.
 *
 * The caller must ensure that `digest_len` bytes are allocated at the location
 * pointed to by `digest`.
 *
 * @param message The input message.
 * @param message_len The input message length in bytes.
 * @param cust_str The customization string.
 * @param cust_str_len The customization string length in bytes.
 * @param[out] digest Output buffer for the result.
 * @param digest_len Requested digest length in bytes.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_kmac_256(kmac_blinded_key_t *key, const uint8_t *message,
                       size_t message_len, const unsigned char *cust_str,
                       size_t cust_str_len, uint8_t *digest, size_t digest_len);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_KMAC_H_
