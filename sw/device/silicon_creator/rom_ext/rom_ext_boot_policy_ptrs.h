// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_ROM_EXT_BOOT_POLICY_PTRS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_ROM_EXT_BOOT_POLICY_PTRS_H_

#include "sw/device/silicon_creator/lib/manifest.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

static_assert((TOP_EARLGREY_EFLASH_SIZE_BYTES % 2) == 0,
              "Flash size is not divisible by 2");

#ifndef OT_OFF_TARGET_TEST
/**
 * Returns a pointer to the manifest of the first owner boot stage image stored
 * in flash slot A.
 *
 * @return Pointer to the manifest of the first owner boot stage image in slot
 * A.
 */
// TODO(#7893): Should these be volatile?
inline const manifest_t *rom_ext_boot_policy_manifest_a_get(void) {
  return (const manifest_t *)(TOP_EARLGREY_EFLASH_BASE_ADDR +
                              MANIFEST_LENGTH_FIELD_ROM_EXT_MAX);
}

/**
 * Returns a pointer to the manifest of the first owner boot stage image stored
 * in flash slot B.
 *
 * @return Pointer to the manifest of the first owner boot stage image in slot
 * B.
 */
inline const manifest_t *rom_ext_boot_policy_manifest_b_get(void) {
  return (const manifest_t *)(TOP_EARLGREY_EFLASH_BASE_ADDR +
                              (TOP_EARLGREY_EFLASH_SIZE_BYTES / 2) +
                              MANIFEST_LENGTH_FIELD_ROM_EXT_MAX);
}
#else
/**
 * Declarations for the functions above that should be defined in tests.
 */
const manifest_t *rom_ext_boot_policy_manifest_a_get(void);
const manifest_t *rom_ext_boot_policy_manifest_b_get(void);
#endif

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_ROM_EXT_BOOT_POLICY_PTRS_H_
