// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_ROM_EXT_MANIFEST_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_ROM_EXT_MANIFEST_H_

#include <stddef.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/manifest.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Return the pointer to rom_ext manifest on the active flash bank.
 */
OT_WARN_UNUSED_RESULT
const manifest_t *rom_ext_manifest(void);

/**
 * These symbols are defined in
 * `opentitan/sw/device/silicon_creator/rom_ext/rom_ext.ld`, and describe the
 * location of the flash header.
 */
extern char _owner_virtual_start_address[];
extern char _owner_virtual_size[];
extern char _rom_ext_size[];
extern char _rom_ext_protected_size[];

/**
 * Compute the virtual address corresponding to the physical address `lma_addr`.
 *
 * @param manifest Pointer to the current manifest.
 * @param lma_addr Load address or physical address.
 * @return the computed virtual address.
 */
OT_WARN_UNUSED_RESULT
inline uintptr_t owner_vma_get(const manifest_t *manifest, uintptr_t lma_addr) {
  return (lma_addr - (uintptr_t)manifest +
          (uintptr_t)_owner_virtual_start_address + (uint32_t)_rom_ext_size);
}

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_ROM_EXT_MANIFEST_H_
