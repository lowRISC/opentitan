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
 * List of supported KMAC modes.
 *
 * We might need to reconsider whether we want to better organize this enum,
 * and if we want to split the large init/update API to individual functions,
 * e.g. kmac_init_sha3(kSha3Length384) or kmac_init_sha3_384().
 */
typedef enum kmac_operation {
  kSHA3_224,
  kSHA3_256,
  kSHA3_384,
  kSHA3_512,
  kSHAKE128,
  kSHAKE256,
  kcSHAKE128,
  kcSHAKE256
} kmac_operation_t;

/**
 * Error return types for KMAC.
 *
 * This is not the exhaustive list, so the fields of this enum are likely to be
 * revised later.
 */
typedef enum kmac_error {
  kKmacOk = 0,
  kKmacInternalError = 1,
  kKmacArgsError = 2,
  kKmacNotImplemented = 3,
} kmac_error_t;

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
kmac_error_t kmac_init(kmac_operation_t operation_type);

/**
 * Feeds the given input string to KMAC core, and produces the digest.
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
 */
OT_WARN_UNUSED_RESULT
kmac_error_t kmac_update(const uint8_t *data, size_t data_len, uint8_t *digest,
                         size_t digest_len);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_KMAC_H_
