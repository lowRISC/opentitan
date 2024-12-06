// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_ROM_EXT_MANIFEST_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_ROM_EXT_MANIFEST_H_

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

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_ROM_EXT_MANIFEST_H_
