// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_USAGE_CONSTRAINTS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_USAGE_CONSTRAINTS_H_

#include "sw/device/silicon_creator/lib/manifest.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Gets the usage constraints struct that is used for verifying boot stage
 * images stored in flash.
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

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_USAGE_CONSTRAINTS_H_
