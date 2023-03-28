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
#include "sw/device/lib/crypto/include/datatypes.h"

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
 * Warning: The caller must ensure that `digest` buffer is large
 * enough to store the resulting digest (at least 224 / 8 = 28 bytes).
 *
 * The caller must ensure that `message` and `digest` have properly
 * allocated `data` fields whose length matches their `len` fields.
 *
 * @param message The input message.
 * @param digest The digest buffer to return the result.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_sha3_224(crypto_const_uint8_buf_t message,
                       crypto_uint8_buf_t *digest);

/**
 * Compute SHA-3-256 in one-shot.
 *
 * Warning: The caller must ensure that `digest` buffer is large
 * enough to store the resulting digest (at least 256 / 8 = 32 bytes).
 *
 * The caller must ensure that `message` and `digest` have properly
 * allocated `data` fields whose length matches their `len` fields.
 *
 * @param message The input message.
 * @param digest The digest buffer to return the result.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_sha3_256(crypto_const_uint8_buf_t message,
                       crypto_uint8_buf_t *digest);
/**
 * Compute SHA-3-384 in one-shot.
 *
 * Warning: The caller must ensure that `digest` buffer is large
 * enough to store the resulting digest (at least 384 / 8 = 48 bytes).
 *
 * The caller must ensure that `message` and `digest` have properly
 * allocated `data` fields whose length matches their `len` fields.
 *
 * @param message The input message.
 * @param digest The digest buffer to return the result.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_sha3_384(crypto_const_uint8_buf_t message,
                       crypto_uint8_buf_t *digest);

/**
 * Compute SHA-3-512 in one-shot.
 *
 * Warning: The caller must ensure that `digest` buffer is large
 * enough to store the resulting digest (at least 512 / 8 = 64 bytes).
 *
 * The caller must ensure that `message` and `digest` have properly
 * allocated `data` fields whose length matches their `len` fields.
 *
 * @param message The input message.
 * @param digest The digest buffer to return the result.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_sha3_512(crypto_const_uint8_buf_t message,
                       crypto_uint8_buf_t *digest);

/**
 * Compute SHAKE-128 in one-shot.
 *
 * Warning: The caller must ensure that `digest->len` contains the
 * requested digest length (in bytes).
 *
 * The caller must ensure that `message` and `digest` have properly
 * allocated `data` fields whose length matches their `len` fields.
 *
 * @param message The input message.
 * @param digest The digest buffer to return the result.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_shake_128(crypto_const_uint8_buf_t message,
                        crypto_uint8_buf_t *digest);

/**
 * Compute SHAKE-256 in one-shot.
 *
 * Warning: The caller must ensure that `digest->len` contains the
 * requested digest length (in bytes).
 *
 * The caller must ensure that `message` and `digest` have properly
 * allocated `data` fields whose length matches their `len` fields.
 *
 * @param message The input message.
 * @param digest The digest buffer to return the result.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_shake_256(crypto_const_uint8_buf_t message,
                        crypto_uint8_buf_t *digest);

/**
 * Compute CSHAKE-128 in one-shot.
 *
 * Warning: The caller must ensure that `digest->len` contains the
 * requested digest length (in bytes).
 *
 * The caller must ensure that `message` and `digest` have properly
 * allocated `data` fields whose length matches their `len` fields.
 *
 * @param message The input message.
 * @param func_name The function name.
 * @param cust_str The customization string.
 * @param digest The digest buffer to return the result.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_cshake_128(crypto_const_uint8_buf_t message,
                         crypto_const_uint8_buf_t func_name,
                         crypto_const_uint8_buf_t cust_str,
                         crypto_uint8_buf_t *digest);

/**
 * Compute CSHAKE-256 in one-shot.
 *
 * Warning: The caller must ensure that `digest->len` contains the
 * requested digest length (in bytes).
 *
 * The caller must ensure that `message` and `digest` have properly
 * allocated `data` fields whose length matches their `len` fields.
 *
 * @param message The input message.
 * @param func_name The function name.
 * @param cust_str The customization string.
 * @param digest The digest buffer to return the result.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_cshake_256(crypto_const_uint8_buf_t message,
                         crypto_const_uint8_buf_t func_name,
                         crypto_const_uint8_buf_t cust_str,
                         crypto_uint8_buf_t *digest);

/**
 * Compute KMAC-128 in one-shot.
 *
 * Warning: The caller must ensure that `digest->len` contains the
 * requested digest length (in bytes).
 *
 * The caller must ensure that `message` and `digest` have properly
 * allocated `data` fields whose length matches their `len` fields.
 *
 * @param key The input key as a struct.
 * @param message The input message.
 * @param func_name The function name.
 * @param cust_str The customization string.
 * @param digest The digest buffer to return the result.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_kmac_128(kmac_blinded_key_t *key,
                       crypto_const_uint8_buf_t message,
                       crypto_const_uint8_buf_t cust_str,
                       crypto_uint8_buf_t *digest);

/**
 * Compute KMAC-256 in one-shot.
 *
 * Warning: The caller must ensure that `digest->len` contains the
 * requested digest length (in bytes).
 *
 * The caller must ensure that `message` and `digest` have properly
 * allocated `data` fields whose length matches their `len` fields.
 *
 * @param key The input key as a struct.
 * @param message The input message.
 * @param func_name The function name.
 * @param cust_str The customization string.
 * @param digest The digest buffer to return the result.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_kmac_256(kmac_blinded_key_t *key,
                       crypto_const_uint8_buf_t message,
                       crypto_const_uint8_buf_t cust_str,
                       crypto_uint8_buf_t *digest);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_KMAC_H_
