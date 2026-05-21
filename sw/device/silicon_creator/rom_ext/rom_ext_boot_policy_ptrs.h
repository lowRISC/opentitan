// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_ROM_EXT_BOOT_POLICY_PTRS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_ROM_EXT_BOOT_POLICY_PTRS_H_

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/base/chip.h"
#include "sw/device/silicon_creator/lib/manifest.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

static_assert((TOP_EARLGREY_EFLASH_SIZE_BYTES % 2) == 0,
              "Flash size is not divisible by 2");

/**
 * Returns the base address of the flash bank containing the given address.
 *
 * This function asserts that the calculated base address is indeed either Bank
 * A or Bank B base address, and triggers a hardened trap on target if the
 * assertion fails (e.g., if the input address is outside the valid flash
 * boundaries).
 *
 * @param addr A physical address in flash.
 * @return The base address of the flash bank (either Bank A or Bank B).
 */
static inline uintptr_t flash_bank_base_get(uintptr_t addr) {
  uintptr_t bank_size = TOP_EARLGREY_EFLASH_SIZE_BYTES / 2;
  uintptr_t bank_base = addr & ~(bank_size - 1);

#if defined(OT_PLATFORM_RV32)
  uintptr_t diff = launder32(bank_base) ^ TOP_EARLGREY_EFLASH_BASE_ADDR;
  HARDENED_CHECK_EQ(diff & ~bank_size, 0);
#endif

  return bank_base;
}

#ifdef OT_PLATFORM_RV32
/**
 * Helper function to scan a flash bank for the first valid owner boot stage
 * manifest.
 *
 * The scan starts at a 64K offset (0x10000) and ends at a 256K offset (0x40000)
 * (excluded) in steps of 8K (0x2000).
 *
 * @param bank_base The base address of the flash bank.
 * @return Pointer to the first found manifest, or NULL if none found.
 */
static inline const manifest_t *rom_ext_boot_policy_manifest_search(
    uintptr_t bank_base) {
  for (uintptr_t offset = 0x10000; offset < 0x40000; offset += 0x2000) {
    const manifest_t *manifest = (const manifest_t *)(bank_base + offset);
    if (manifest->identifier == CHIP_BL0_IDENTIFIER) {
      return manifest;
    }
  }
  return NULL;
}

/**
 * Returns a pointer to the manifest of the first owner boot stage image stored
 * in flash slot A.
 *
 * @return Pointer to the manifest of the first owner boot stage image in slot
 * A.
 */
OT_WARN_UNUSED_RESULT
static inline const manifest_t *rom_ext_boot_policy_manifest_a_get(void) {
  return rom_ext_boot_policy_manifest_search(TOP_EARLGREY_EFLASH_BASE_ADDR);
}

/**
 * Returns a pointer to the manifest of the first owner boot stage image stored
 * in flash slot B.
 *
 * @return Pointer to the manifest of the first owner boot stage image in slot
 * B.
 */
OT_WARN_UNUSED_RESULT
static inline const manifest_t *rom_ext_boot_policy_manifest_b_get(void) {
  return rom_ext_boot_policy_manifest_search(
      TOP_EARLGREY_EFLASH_BASE_ADDR + (TOP_EARLGREY_EFLASH_SIZE_BYTES / 2));
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
