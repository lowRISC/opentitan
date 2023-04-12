// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_INTEGRITY_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_INTEGRITY_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/crypto/include/datatypes.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Compute the checksum of an unblinded key.
 *
 * The current key checksum is ignored. Call this routine after modifying
 * blinded key material (e.g. for re-masking).
 *
 * @param key Unblinded key.
 * @returns Checksum value.
 */
uint32_t integrity_unblinded_checksum(const crypto_unblinded_key_t *key);

/**
 * Compute the checksum of a blinded key.
 *
 * The current key checksum is ignored. Call this routine after modifying
 * blinded key material (e.g. for re-masking).
 *
 * @param key Blinded key.
 * @returns Checksum value.
 */
uint32_t integrity_blinded_checksum(const crypto_blinded_key_t *key);

/**
 * Perform an integrity check on the unblinded key.
 *
 * Returns `kHardenedBoolTrue` if the check passed and `kHardenedBoolFalse`
 * otherwise.
 *
 * @param key Unblinded key.
 * @returns Whether the integrity check passed.
 */
OT_WARN_UNUSED_RESULT
hardened_bool_t integrity_unblinded_key_check(
    const crypto_unblinded_key_t *key);

/**
 * Perform an integrity check on the blinded key.
 *
 * Returns `kHardenedBoolTrue` if the check passed and `kHardenedBoolFalse`
 * otherwise.
 *
 * @param key Blinded key.
 * @returns Whether the integrity check passed.
 */
OT_WARN_UNUSED_RESULT
hardened_bool_t integrity_blinded_key_check(const crypto_blinded_key_t *key);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_INTEGRITY_H_
