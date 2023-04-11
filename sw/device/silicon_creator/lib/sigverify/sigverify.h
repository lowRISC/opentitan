// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SIGVERIFY_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SIGVERIFY_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/lib/sigverify/rsa_verify.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * Correct `flash_exec` value.
   *
   * This value must be equal to `FLASH_CTRL_PARAM_EXEC_EN`. Defined here to be
   * able to use in tests.
   */
  kSigverifyFlashExec = 0xa26a38f7,
};


/**
 * Gets the usage constraints struct that is used for verifying a ROM_EXT.
 *
 * This function reads
 * - The device identifier from the life cycle controller,
 * - Creator and owner manufacturing states from the OTP,
 * - The life cycle state from life cycle controller, and
 * masks the fields of `usage_constraints` according to the given
 * `selector_bits`.
 *
 * See also: `manifest_usage_constraints_t`.
 *
 * @param selector_bits Selector bits of the manifest of the ROM_EXT to be
 * verified.
 * @param[out] usage_constraints Usage constraints.
 */
void sigverify_usage_constraints_get(
    uint32_t selector_bits, manifest_usage_constraints_t *usage_constraints);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SIGVERIFY_H_
