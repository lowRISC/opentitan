// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_ROM_EXT_VERIFY_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_ROM_EXT_VERIFY_H_

#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/lib/ownership/owner_block.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Verify the the next boot stage according to the owner configuration.
 *
 * @param manifest Pointer to the manifest being examined.
 * @param slot_id Name of the slot being examined ('A', 'B' or 0).  This
 *                parameter controls the "verify" debug print, but is not used
 *                for any verification purpose.
 * @param boot_data Pointer to the boot_data struct.
 * @param flash_exec[out] Redundant check word for image validity.
 * @param keyring A list of valid owner Application keys.
 * @param verify_key[out] Key selected for verification.
 * @param owner_config The owner configuration.
 * @param isfb_check_count[out] The number of checks performed by ISFB (if
 *                              present).
 * @return kErrorOk or a validation error.
 */
OT_WARN_UNUSED_RESULT
rom_error_t rom_ext_verify(const manifest_t *manifest, char slot_id,
                           const boot_data_t *boot_data, uint32_t *flash_exec,
                           owner_application_keyring_t *keyring,
                           size_t *verify_key, owner_config_t *owner_config,
                           uint32_t *isfb_check_count);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_ROM_EXT_VERIFY_H_
