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

OT_WARN_UNUSED_RESULT
rom_error_t rom_ext_verify(const manifest_t *manifest,
                           const boot_data_t *boot_data, uint32_t *flash_exec,
                           owner_application_keyring_t *keyring,
                           size_t *verify_key, owner_config_t *owner_config,
                           uint32_t *isfb_check_count);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_ROM_EXT_VERIFY_H_
