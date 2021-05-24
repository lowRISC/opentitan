// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_ROMEXTIMAGE_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_ROMEXTIMAGE_H_

#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/manifest.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Type alias for the ROM_EXT entry point.
 *
 * The entry point address obtained from the ROM_EXT manifest must be cast to a
 * pointer to this type before being called.
 */
typedef void romextimage_entry_point(void);

enum {
  /**
   * ROM_EXT manifest identifier (ASCII "OTRE").
   */
  kRomextimageManifestIdentifier = 0x4552544f,
};

/**
 * Gets the manifest of the ROM_EXT image in the given slot.
 *
 * This function also checks that the manifest's identifier field has the
 * expected value.
 *
 * @param slot A flash slot.
 * @param[out] The manifest of the ROM_EXT image in the given slot.
 * @return The result of the operation.
 */
rom_error_t romextimage_manifest_get(flash_slot_t slot,
                                     const manifest_t **manifest);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_ROMEXTIMAGE_H_
