// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_KMAC_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_KMAC_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
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
 * Security strength values.
 *
 * These values corresponds to the half of the capacity of Keccak permutation.
 */
typedef enum kmac_security_str {
  kKmacSecurityStrength128 = 0,
  kKmacSecurityStrength224 = 1,
  kKmacSecurityStrength256 = 2,
  kKmacSecurityStrength384 = 3,
  kKmacSecurityStrength512 = 4,
} kmac_security_str_t;

/**
 * List of supported KMAC modes.
 *
 * Each `kmac_operation_t` enumeration constant is a bitfield with the
 * following layout:
 * - Bit 0: kmac_en (Whether to enable KMAC datapath).
 * - Bit 1-2: Keccak hashing mode (e.g. SHA, SHAKE, or cSHAKE).
 */
typedef enum kmac_operation {
  kKmacOperationSHA3 = (0 << 1) | 0,
  kKmacOperationSHAKE = (2 << 1) | 0,
  kKmacOperationCSHAKE = (3 << 1) | 0,
  kKmacOperationKMAC = (3 << 1) | 1,
} kmac_operation_t;

/**
 * List of supported KMAC key sizes.
 */
typedef enum kmac_key_length {
  kKmacKeyLength128 = 0,
  kKmacKeyLength192 = 1,
  kKmacKeyLength256 = 2,
  kKmacKeyLength384 = 3,
  kKmacKeyLength512 = 4,
} kmac_key_len_t;

/**
 * Error return types for KMAC.
 *
 * This is not the exhaustive list, so the fields of this enum are likely to be
 * revised later.
 */
typedef enum kmac_error {
  kKmacOk = 0,
  kKmacInternalError,
  kKmacNotIdle,
  kKmacCfgWriteDisabled,
  kKmacIntrErrPending,
  kKmacCfgDisabledError,
  kKmacFatalFaultError,
  kKmacRecovFaultError,
  kKmacArgsError,
  kKmacDigestLenTooLongError,
  kKmacUnsupportedKeySizeError,
  kKmacNotImplemented,
  kKmacCustomPaddingError,
  kKmacUnsupportedPaddingLength,
} kmac_error_t;

/**
 * Simplified key struct to pass blinded key internally.
 */
typedef struct kmac_blinded_key {
  const uint32_t *share0;
  const uint32_t *share1;
  // The length of single share (in bytes)
  size_t len;
} kmac_blinded_key_t;

/**
 * Return the matching enum of `kmac_key_len_t` for given key length.
 *
 * `key_len_enum` must not be NULL pointer.
 *
 * @param key_len The size of the key in bytes.
 * @param key_len_enum The corresponding enum value to be returned.
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
kmac_error_t kmac_get_key_len_bytes(size_t key_len,
                                    kmac_key_len_t *key_len_enum);

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
kmac_error_t kmac_hwip_default_configure(void);

/**
 * Initializes the KMAC configuration.
 *
 * In particular, this function sets the CFG register of KMAC for given
 * `operation_type`. The struct type kmac_operation_t is defined in a way that
 * each field inherently implies a fixed security strength (i.e. half of Keccak
 * capacity). For instance, if we want to run SHA-3 with 224-bit digest size,
 * then `operation_type` = kSHA3_224.
 *
 *
 * @param operation The chosen operation, see kmac_operation_t struct.
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
kmac_error_t kmac_init(kmac_operation_t operation,
                       kmac_security_str_t security_str);

/**
 * Configure the prefix registers with customization string.
 *
 * For KMAC, this function ignores `func_name` and uses "KMAC" instead.
 *
 * The caller must ensure that `func_name` and `cust_str` have properly
 * allocated `data` fields whose length matches their `len` fields.
 *
 * In total `func_name` and `cust_str` can be at most `kKmacPrefixMaxSize`
 * bytes.
 *
 * @param operation The KMAC or cSHAKE operation.
 * @param func_name The function name, used for cSHAKE.
 * @param cust_str The customization string (both for cSHAKE and KMAC).
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
kmac_error_t kmac_write_prefix_block(kmac_operation_t operation,
                                     crypto_const_uint8_buf_t func_name,
                                     crypto_const_uint8_buf_t cust_str);

/**
 * Update the key registers with given key shares.
 *
 * The caller must ensure that `key` struct is properly populated (no NULL
 * pointers and matching `len`).
 *
 * The accepted `key->len` values are {128 / 8, 192 / 8, 256 / 8, 384 / 8,
 * 512 / 8}, otherwise an error will be returned.
 *
 * @param key The input key passed as a struct.
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
kmac_error_t kmac_write_key_block(kmac_blinded_key_t *key);

/**
 * Common routine for feeding message blocks during SHA/SHAKE/cSHAKE/KMAC.
 *
 * Before running this, the operation type must be configured with kmac_init.
 * Then, we can use this function to feed various bytes of data to the KMAC
 * core. Note that this is a one-shot implementation, and it does not support
 * streaming mode. This decision is in accord with OpenTitan's Crypto Library
 * Specification. Refer to the Hash section of this specification.
 *
 * Current implementation has few limitiations:
 *
 * 1. `message.data` pointer is assumed to be word-aligned. The case where
 * `data` field is not divisible by 4 is not yet implemented. This is about
 * extra protection against SCA.
 *
 * 2. Currently, there is no error check on consisteny of the input parameters.
 * For instance, one can invoke SHA-3_224 with digest_len=32, which will produce
 * 256 bits of digest.
 *
 * The caller must ensure that `message` and `digest` have properly
 * allocated `data` fields whose length matches their `len` fields.
 *
 * @param operation The operation type.
 * @param message Input message string.
 * @param digest The struct to which the result will be written.
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
kmac_error_t kmac_process_msg_blocks(kmac_operation_t operation,
                                     crypto_const_uint8_buf_t message,
                                     crypto_uint8_buf_t *digest);

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
kmac_error_t kmac_sha3_224(crypto_const_uint8_buf_t message,
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
kmac_error_t kmac_sha3_256(crypto_const_uint8_buf_t message,
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
kmac_error_t kmac_sha3_384(crypto_const_uint8_buf_t message,
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
kmac_error_t kmac_sha3_512(crypto_const_uint8_buf_t message,
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
kmac_error_t kmac_shake_128(crypto_const_uint8_buf_t message,
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
kmac_error_t kmac_shake_256(crypto_const_uint8_buf_t message,
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
kmac_error_t kmac_cshake_128(crypto_const_uint8_buf_t message,
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
kmac_error_t kmac_cshake_256(crypto_const_uint8_buf_t message,
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
kmac_error_t kmac_kmac_128(kmac_blinded_key_t *key,
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
kmac_error_t kmac_kmac_256(kmac_blinded_key_t *key,
                           crypto_const_uint8_buf_t message,
                           crypto_const_uint8_buf_t cust_str,
                           crypto_uint8_buf_t *digest);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_KMAC_H_
