// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/bootstrap.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "flash_ctrl_regs.h"

// Slot address defined in bazel
extern char _flash_rom_slot[];

rom_error_t bootstrap_chip_erase(void) {
  flash_ctrl_bank_erase_perms_set(kHardenedBoolTrue);
  HARDENED_RETURN_IF_ERROR(flash_ctrl_data_erase(0, kFlashCtrlEraseTypeBank));
  // Erase until the start of the flash ROM region to prevent
  // the code from erasing itself.
  flash_ctrl_data_default_perms_set((flash_ctrl_perms_t){
      .read = kMultiBitBool4False,
      .write = kMultiBitBool4False,
      .erase = kMultiBitBool4True,
  });
  for (uint32_t addr = FLASH_CTRL_PARAM_BYTES_PER_BANK;
       addr < (uint32_t)_flash_rom_slot;
       addr += FLASH_CTRL_PARAM_BYTES_PER_PAGE) {
    HARDENED_RETURN_IF_ERROR(
        flash_ctrl_data_erase(addr, kFlashCtrlEraseTypePage));
  }
  flash_ctrl_data_default_perms_set((flash_ctrl_perms_t){
      .read = kMultiBitBool4False,
      .write = kMultiBitBool4False,
      .erase = kMultiBitBool4False,
  });
  flash_ctrl_bank_erase_perms_set(kHardenedBoolFalse);
  return kErrorOk;
}

rom_error_t bootstrap_erase_verify(void) {
  HARDENED_RETURN_IF_ERROR(
      flash_ctrl_data_erase_verify(0, kFlashCtrlEraseTypeBank));
  for (uint32_t addr = FLASH_CTRL_PARAM_BYTES_PER_BANK;
       addr < (uint32_t)_flash_rom_slot;
       addr += FLASH_CTRL_PARAM_BYTES_PER_PAGE) {
    HARDENED_RETURN_IF_ERROR(
        flash_ctrl_data_erase_verify(addr, kFlashCtrlEraseTypePage));
  }
  return kErrorOk;
}
