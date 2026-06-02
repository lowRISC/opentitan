// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_SIGVERIFY_KEYS_SPX_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_SIGVERIFY_KEYS_SPX_H_

#include <stdint.h>

#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/rom/sigverify_key_types.h"
#include "sw/device/silicon_creator/rom/sigverify_otp_keys.h"
#include "sw/lib/sw/device/silicon_creator/error.h"
#include "sw/lib/sw/device/silicon_creator/sigverify/spx_key.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Number of SPX public keys.
 */
extern const size_t kSigverifySpxKeysCnt;

/**
 * Step size to use when checking SPX public keys.
 *
 * This must be coprime with and less than `kSigverifyNumSpxKeys`.
 * Note: Step size is not applicable when `kSigverifyNumSpxKeys` is 1.
 */
extern const size_t kSigverifySpxKeysStep;

/**
 * Public keys for signature verification.
 */
extern const sigverify_rom_spx_key_t kSigverifySpxKeys[];

/**
 * Returns the key with the given ID.
 *
 * This function returns the key only if it can be used in the given life cycle
 * state and is valid in OTP. OTP check is performed only if the device is in a
 * non-test operational state (PROD, PROD_END, DEV, RMA).
 *
 * @param key_id A key ID.
 * @param lc_state Life cycle state of the device.
 * @param key Key with the given ID, valid only if it exists.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t sigverify_spx_key_get(const sigverify_otp_key_ctx_t *sigverify_ctx,
                                  uint32_t key_id, lifecycle_state_t lc_state,
                                  const sigverify_spx_key_t **key);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_SIGVERIFY_KEYS_SPX_H_
