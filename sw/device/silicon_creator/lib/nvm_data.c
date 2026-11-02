// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/base/chip.h"
#include "sw/device/silicon_creator/lib/nvm_ctrl.h"

rom_error_t nvm_data_load(nvm_data_id_t data_id) {
  (void)data_id;
  return kErrorOk;
}

void nvm_data_unload(nvm_data_id_t data_id) { (void)data_id; }

rom_error_t nvm_data_get(nvm_data_id_t data_id, void **data_ptr,
                         uint32_t *data_size) {
  void *ret_ptr = NULL;
  uint32_t ret_size = 0u;
  switch (data_id) {
    case kNvmDataIdRomExtManifestSlotA:
      ret_ptr = (void *)NVM_DATA_BASE_ADDR;
      ret_size = CHIP_MANIFEST_SIZE;
      break;
    case kNvmDataIdRomExtSlotA:
      ret_ptr = (void *)NVM_DATA_BASE_ADDR;
      ret_size = CHIP_ROM_EXT_SIZE_MAX;
      break;
    case kNvmDataIdRomExtManifestSlotB:
      ret_ptr = (void *)(NVM_DATA_BASE_ADDR + NVM_BYTES_PER_SLOT);
      ret_size = CHIP_MANIFEST_SIZE;
      break;
    case kNvmDataIdRomExtSlotB:
      ret_ptr = (void *)(NVM_DATA_BASE_ADDR + NVM_BYTES_PER_SLOT);
      ret_size = CHIP_ROM_EXT_SIZE_MAX;
      break;
    case kNvmDataIdBl0ManifestSlotA:
      ret_ptr = (void *)(NVM_DATA_BASE_ADDR + CHIP_ROM_EXT_SIZE_MAX);
      ret_size = CHIP_MANIFEST_SIZE;
      break;
    case kNvmDataIdBl0SlotA:
      ret_ptr = (void *)(NVM_DATA_BASE_ADDR + CHIP_ROM_EXT_SIZE_MAX);
      ret_size = CHIP_BL0_SIZE_MAX;
      break;
    case kNvmDataIdBl0ManifestSlotB:
      ret_ptr = (void *)(NVM_DATA_BASE_ADDR + NVM_BYTES_PER_SLOT +
                         CHIP_ROM_EXT_SIZE_MAX);
      ret_size = CHIP_MANIFEST_SIZE;
      break;
    case kNvmDataIdBl0SlotB:
      ret_ptr = (void *)(NVM_DATA_BASE_ADDR + NVM_BYTES_PER_SLOT +
                         CHIP_ROM_EXT_SIZE_MAX);
      ret_size = CHIP_BL0_SIZE_MAX;
      break;
    default:
      HARDENED_TRAP();
  }
  if (data_ptr != NULL) {
    *data_ptr = ret_ptr;
  }
  if (data_size != NULL) {
    *data_size = ret_size;
  }
  return kErrorOk;
}
