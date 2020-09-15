
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_MASK_ROM_ROM_EXT_MANIFEST_H_
#define OPENTITAN_SW_DEVICE_MASK_ROM_ROM_EXT_MANIFEST_H_

// TODO: Doc page
/**
 * @file
 * @brief <a href="">ROM EXT Manifest</a>
 */

#include <stdint.h>

// Header Extern Guard (so header can be used from C and C++)
#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * ROM EXT Manifest.
 */
typedef struct rom_ext_manifest {
  uint32_t key_id;
} rom_ext_manifest_t;

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_MASK_ROM_ROM_EXT_MANIFEST_H_
