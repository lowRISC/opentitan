// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_KMAC_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_KMAC_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"

#ifdef __cplusplus
extern "C" {
#endif

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
 * We might need to reconsider whether we want to better organize this enum,
 * and if we want to split the large init/update API to individual functions,
 * e.g. kmac_init_sha3(kSha3Length384) or kmac_init_sha3_384().
 */
typedef enum kmac_operation {
  kKmacOperationSHA3,
  kKmacOperationSHAKE,
  kKmacOperationCSHAKE,
  kKmacOperationKMAC,
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
 * @param operation_type The chosen operation, see kmac_operation_t struct.
 * @return Error of type kmac_error_t.
 */
OT_WARN_UNUSED_RESULT
kmac_error_t kmac_init(kmac_operation_t operation,
                       kmac_security_str_t security_str,
                       const uint8_t *func_name, uint8_t func_name_len,
                       const uint8_t *cust_str, size_t cust_str_len);

/**
 * Configure the prefix registers with customization string.
 *
 * For KMAC, this function ignores `func_name` and uses "KMAC" instead.
 *
 * @param operation The KMAC or cSHAKE operation.
 * @param func_name The function name, used for cSHAKE.
 * @param func_name_len The byte size of `func_name`.
 * @param cust_str The customization string.
 * @param cust_str_len The byte size of `cust_str`.
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
kmac_error_t kmac_write_prefix_block(kmac_operation_t operation,
                                     const uint8_t *func_name,
                                     const size_t func_name_len,
                                     const uint8_t *cust_str,
                                     const size_t cust_str_len);

/**
 * Update the key registers with given key.
 *
 * @param key The input key array.
 * @param key_len The size of key from enum type kmac_key_len_t.
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
kmac_error_t kmac_write_key_block(const uint8_t *key, kmac_key_len_t key_len);

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
 * 1. `data` pointer is assumed to be word-aligned. The case where `data` is not
 * divisible by 4 is not yet implemented.
 * 2. Currently, there is no error check on consisteny of the input parameters.
 * For instance, one can invoke SHA-3_224 with digest_len=32, which will produce
 * 256 bits of digest.
 *
 * Requirements:
 * 1. The caller must ensure that `digest` is large enough to accommodate
 * `digest_len` bytes.
 *
 * @param data Byte pointer to the input string.
 * @param data_len The number of bytes pointed by `data`.
 * @param digest The buffer to which the result will be written.
 * @param digest_len The length of the digest, i.e. the number of bytes read
 * from the final Keccak state.
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
kmac_error_t kmac_process_msg_blocks(kmac_operation_t operation,
                                     const uint8_t *data, size_t data_len,
                                     uint8_t *digest, size_t digest_len);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_KMAC_H_
