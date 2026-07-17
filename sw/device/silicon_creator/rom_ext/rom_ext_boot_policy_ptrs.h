// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_ROM_EXT_BOOT_POLICY_PTRS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_ROM_EXT_BOOT_POLICY_PTRS_H_

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/base/chip.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/rom_ext/rom_ext_boot_policy.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

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
 * Searches for a valid manifest within a bank.
 *
 * This function checks specific OwnerSW offsets in the bank (88K and 64K
 * by default, or 168K and 128K when coverage is enabled) in descending order.
 *
 * @param bank_base The base address of the bank (Slot A or B base).
 * @param boot_data The boot data for the current lifecycle state.
 * @return Pointer to the first valid manifest found, or the manifest at the
 *         lowest offset as a candidate if none are valid.
 */
OT_WARN_UNUSED_RESULT
const manifest_t *rom_ext_boot_policy_manifest_search(
    uintptr_t bank_base, const boot_data_t *boot_data);

static_assert((TOP_EARLGREY_EFLASH_SIZE_BYTES % 2) == 0,
              "Flash size is not divisible by 2");

#ifdef OT_PLATFORM_RV32

/**
 * Returns a pointer to the manifest of the first owner boot stage image stored
 * in flash slot A.
 *
 * @param boot_data Boot data struct.
 * @return Pointer to the manifest of the first owner boot stage image in slot
 * A.
 */
OT_WARN_UNUSED_RESULT
static inline const manifest_t *rom_ext_boot_policy_manifest_a_get(
    const boot_data_t *boot_data) {
  return rom_ext_boot_policy_manifest_search(TOP_EARLGREY_EFLASH_BASE_ADDR,
                                             boot_data);
}

/**
 * Returns a pointer to the manifest of the first owner boot stage image stored
 * in flash slot B.
 *
 * @param boot_data Boot data struct.
 * @return Pointer to the manifest of the first owner boot stage image in slot
 * B.
 */
OT_WARN_UNUSED_RESULT
static inline const manifest_t *rom_ext_boot_policy_manifest_b_get(
    const boot_data_t *boot_data) {
  return rom_ext_boot_policy_manifest_search(
      TOP_EARLGREY_EFLASH_BASE_ADDR + (TOP_EARLGREY_EFLASH_SIZE_BYTES / 2),
      boot_data);
}
#else
/**
 * Declarations for the functions above that should be defined in tests.
 */
const manifest_t *rom_ext_boot_policy_manifest_a_get(
    const boot_data_t *boot_data);
const manifest_t *rom_ext_boot_policy_manifest_b_get(
    const boot_data_t *boot_data);
#endif

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_ROM_EXT_BOOT_POLICY_PTRS_H_
