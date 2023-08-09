// Copyright lowRISC contributors.
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
 * Type alias for the first owner boot stage entry point.
 *
 * The entry point address obtained from the first owner boot stage manifest
 * must be cast to a pointer to this type before being called.
 */
typedef void owner_stage_entry_point(void);

/**
 * Manifests of first boot owner boot stages in descending order according to
 * their security versions.
 *
 * These boot stages must be verified prior to handing over execution.
 */
typedef struct rom_ext_boot_policy_manifests {
  /**
   * First owner boot stage manifests in descending order according to
   * their security versions.
   */
  const manifest_t *ordered[2];
} rom_ext_boot_policy_manifests_t;

/**
 * Returns the manifests of first owner boot stages that should be attempted to
 * boot in descending order according to their security versions.
 *
 * These boot stages must be verified prior to handing over execution.
 *
 * @param boot_data Boot data struct.
 * @return Manifests of first owner boot stages in descending order according to
 * their security versions.
 */
OT_WARN_UNUSED_RESULT
rom_ext_boot_policy_manifests_t rom_ext_boot_policy_manifests_get(
    const boot_data_t *boot_data);

/**
 * Checks the fields of a first owner boot stage manifest.
 *
 * This function performs bounds checks on the fields of the manifest, checks
 * that its `identifier` is correct, and its `security_version` is greater than
 * or equal to the minimum required security version.
 *
 * @param manifest A first boot owner boot stage manifest.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t rom_ext_boot_policy_manifest_check(const manifest_t *manifest);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_ROM_EXT_BOOT_POLICY_H_
