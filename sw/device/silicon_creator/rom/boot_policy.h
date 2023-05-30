// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_BOOT_POLICY_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_BOOT_POLICY_H_

#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/manifest.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Type alias for the ROM_EXT entry point.
 *
 * The entry point address obtained from the ROM_EXT manifest must be cast to a
 * pointer to this type before being called.
 */
typedef void rom_ext_entry_point(void);

/**
 * Manifests of ROM_EXTs in descending order according to their security
 * versions.
 *
 * These ROM_EXTs must be verified prior to handing over execution.
 */
typedef struct boot_policy_manifests {
  /**
   * ROM_EXT manifests in descending order according to their security versions.
   */
  const manifest_t *ordered[2];
} boot_policy_manifests_t;

/**
 * Returns the manifests of ROM_EXTs that should be attempted to boot in
 * descending order according to their security versions.
 *
 * These ROM_EXTs must be verified prior to handing over execution.
 *
 * @return Manifests of ROM_EXTs in descending order according to their
 * security versions.
 */
OT_WARN_UNUSED_RESULT
boot_policy_manifests_t boot_policy_manifests_get(void);

/**
 * Checks the fields of a ROM_EXT manifest.
 *
 * This function performs bounds checks on the fields of the manifest, checks
 * that its `identifier` is correct, and its `security_version` is greater than
 * or equal to the minimum required security version.
 *
 * @param manifest A ROM_EXT manifest.
 * @param boot_data Boot data.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t boot_policy_manifest_check(const manifest_t *manifest,
                                       const boot_data_t *boot_data);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_BOOT_POLICY_H_
