// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_ROM_EXT_BOOT_POLICY_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_ROM_EXT_BOOT_POLICY_H_

#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/manifest.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Checks the fields of a first owner boot stage manifest.
 *
 * This function performs bounds checks on the fields of the manifest, checks
 * that its `identifier` is correct, and its `security_version` is greater than
 * or equal to the minimum required security version.
 *
 * @param manifest A first boot owner boot stage manifest.
 * @param boot_data The boot data for the current lifecycle state.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t rom_ext_boot_policy_manifest_check(const manifest_t *manifest,
                                               const boot_data_t *boot_data);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_ROM_EXT_BOOT_POLICY_H_
