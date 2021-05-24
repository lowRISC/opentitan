// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/mask_rom/romextimage.h"

#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/mask_rom/romextimage_ptrs.h"

rom_error_t romextimage_manifest_get(flash_slot_t slot,
                                     const manifest_t **manifest) {
  const manifest_t *ptr;
  switch (slot) {
    case kFlashSlotA:
      ptr = romextimage_slot_a_manifest_ptr_get();
      break;
    case kFlashSlotB:
      ptr = romextimage_slot_b_manifest_ptr_get();
      break;
    default:
      return kErrorRomextimageInvalidArgument;
  }
  if (ptr->identifier != kRomextimageManifestIdentifier) {
    return kErrorRomextimageInternal;
  }
  *manifest = ptr;
  return kErrorOk;
}

extern const manifest_t *romextimage_slot_a_manifest_ptr_get(void);
extern const manifest_t *romextimage_slot_b_manifest_ptr_get(void);
