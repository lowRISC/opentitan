// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_ROM_EXT_BOOT_POLICY_PTRS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_ROM_EXT_BOOT_POLICY_PTRS_H_

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/base/chip.h"
#include "sw/device/silicon_creator/lib/manifest.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

#ifdef OT_PLATFORM_RV32
// Only needed by the inline definitions below: the host/mock build compiles
// this header too (via mock_rom_ext_boot_policy_ptrs.cc), but only declares
// the plain function prototypes in the #else branch, so it must not require
// nvm_ctrl.h (which isn't a host dependency, and isn't buildable for every
// top -- see nvm_ctrl.h/rram_ctrl.h).
#include "sw/device/silicon_creator/lib/nvm_ctrl.h"

static_assert((NVM_DATA_SIZE_BYTES % 2) == 0, "NVM size is not divisible by 2");
/**
 * Returns a pointer to the manifest of the first owner boot stage image stored
 * in NVM slot A.
 *
 * @return Pointer to the manifest of the first owner boot stage image in slot
 * A.
 */
OT_WARN_UNUSED_RESULT
inline const manifest_t *rom_ext_boot_policy_manifest_a_get(void) {
  return (const manifest_t *)(NVM_DATA_BASE_ADDR + CHIP_ROM_EXT_SIZE_MAX);
}

/**
 * Returns a pointer to the manifest of the first owner boot stage image stored
 * in NVM slot B.
 *
 * @return Pointer to the manifest of the first owner boot stage image in slot
 * B.
 */
OT_WARN_UNUSED_RESULT
inline const manifest_t *rom_ext_boot_policy_manifest_b_get(void) {
  return (const manifest_t *)(NVM_DATA_BASE_ADDR + (NVM_DATA_SIZE_BYTES / 2) +
                              CHIP_ROM_EXT_SIZE_MAX);
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
