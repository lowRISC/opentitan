// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_ROMEXTIMAGE_PTRS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_ROMEXTIMAGE_PTRS_H_

#include "sw/device/silicon_creator/lib/manifest.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

static_assert((TOP_EARLGREY_EFLASH_SIZE_BYTES % 2) == 0,
              "Flash size is not divisible by 2");

#ifndef OT_OFF_TARGET_TEST
/**
 * Returns a pointer to the manifest of the ROM_EXT image stored in flash
 * slot A.
 *
 * @return Pointer to the manifest of the ROM_EXT image in slot A.
 */
inline const manifest_t *romextimage_slot_a_manifest_ptr_get(void) {
  return (const manifest_t *)TOP_EARLGREY_EFLASH_BASE_ADDR;
}

/**
 * Returns a pointer to the manifest of the ROM_EXT image stored in flash
 * slot B.
 *
 * @return Pointer to the manifest of the ROM_EXT image in slot B.
 */
inline const manifest_t *romextimage_slot_b_manifest_ptr_get(void) {
  return (const manifest_t *)(TOP_EARLGREY_EFLASH_BASE_ADDR +
                              (TOP_EARLGREY_EFLASH_SIZE_BYTES / 2));
}
#else
/**
 * Declarations for the functions above that should be defined in tests.
 */
const manifest_t *romextimage_slot_a_manifest_ptr_get(void);
const manifest_t *romextimage_slot_b_manifest_ptr_get(void);
#endif

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_ROMEXTIMAGE_PTRS_H_
