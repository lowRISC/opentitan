// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_ROM_EXT_MANIFEST_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_ROM_EXT_MANIFEST_H_

#include <stddef.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/manifest.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Return the pointer to rom_ext manifest on the active flash bank.
 */
OT_WARN_UNUSED_RESULT
const manifest_t *rom_ext_manifest(void);

#if !defined(OT_PLATFORM_RV32)
/**
 * Global variable for configuring the return value of `rom_ext_manifest()`
 * in host unit tests.
 */
extern const manifest_t *_rom_ext_manifest_test_value;
#endif

/**
 * These symbols are defined in
 * `opentitan/sw/device/silicon_creator/rom_ext/rom_ext.ld`, and describe the
 * location of the flash header.
 */
extern char _owner_virtual_start_address[];
extern char _owner_virtual_size[];
extern char _rom_ext_size[];

/**
 * Compute the virtual address corresponding to the physical address `lma_addr`.
 *
 * @param lma_addr Load address or physical address.
 * @return the computed virtual address.
 */
OT_WARN_UNUSED_RESULT
inline uintptr_t owner_vma_get(uintptr_t lma_addr) {
  uintptr_t bank_mask = (TOP_EARLGREY_EFLASH_SIZE_BYTES / 2) - 1;
  return (lma_addr & bank_mask) + (uintptr_t)_owner_virtual_start_address;
}

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_ROM_EXT_MANIFEST_H_
