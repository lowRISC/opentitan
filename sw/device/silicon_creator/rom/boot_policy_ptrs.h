// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_BOOT_POLICY_PTRS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_BOOT_POLICY_PTRS_H_

#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/lib/nvm_ctrl.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

#ifdef OT_PLATFORM_RV32
/**
 * Returns a pointer to the manifest of the ROM_EXT image stored in NVM
 * slot A.
 *
 * @return Pointer to the manifest of the ROM_EXT image in slot A.
 */
OT_WARN_UNUSED_RESULT
inline const manifest_t *boot_policy_manifest_a_load(void) {
  void *ptr = NULL;
  if (nvm_data_load(kNvmDataIdRomExtManifestSlotA) != kErrorOk)
    return NULL;
  if (nvm_data_get(kNvmDataIdRomExtManifestSlotA, &ptr, NULL) != kErrorOk)
    return NULL;
  return ptr;
}

/**
 * Returns a pointer to the manifest of the ROM_EXT image stored in NVM
 * slot B.
 *
 * @return Pointer to the manifest of the ROM_EXT image in slot B.
 */
OT_WARN_UNUSED_RESULT
inline const manifest_t *boot_policy_manifest_b_load(void) {
  void *ptr = NULL;
  if (nvm_data_load(kNvmDataIdRomExtManifestSlotB) != kErrorOk)
    return NULL;
  if (nvm_data_get(kNvmDataIdRomExtManifestSlotB, &ptr, NULL) != kErrorOk)
    return NULL;
  return ptr;
}

inline void boot_policy_manifest_a_unload(void) {
  nvm_data_unload(kNvmDataIdRomExtManifestSlotA);
}

inline void boot_policy_manifest_b_unload(void) {
  nvm_data_unload(kNvmDataIdRomExtManifestSlotB);
}

#else
/**
 * Declarations for the functions above that should be defined in tests.
 */
const manifest_t *boot_policy_manifest_a_load(void);
const manifest_t *boot_policy_manifest_b_load(void);
void boot_policy_manifest_a_unload(void);
void boot_policy_manifest_b_unload(void);
#endif  // OT_PLATFORM_RV32

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_BOOT_POLICY_PTRS_H_
