// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/ctn_sram.h"

#include <assert.h>

#include "sw/lib/sw/device/base/abs_mmio.h"
#include "sw/lib/sw/device/base/hardened.h"
#include "sw/lib/sw/device/base/memory.h"
#include "sw/lib/sw/device/base/multibits.h"

#include "flash_ctrl_regs.h"  // Generated.
#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"
#include "sram_ctrl_regs.h"  // Generated.

enum {
  /*
   * Base ctn sram address, exclusive.
   */
  kBaseAddress = TOP_DARJEELING_RAM_CTN_BASE_ADDR,
  /*
   * Maximum ctn sram size to be used as flash, exclusive.
   */
  kMaxSize = FLASH_CTRL_PARAM_BYTES_PER_BANK * FLASH_CTRL_PARAM_REG_NUM_BANKS,
  /**
   * Value of a word in sram after erase.
   */
  kErasedWord = UINT32_MAX,
};

static_assert(kMaxSize <= TOP_DARJEELING_RAM_CTN_SIZE_BYTES,
              "CTN SRAM area for image bootstap must be smaller than total.");

rom_error_t ctn_sram_data_write(uint32_t addr, uint32_t len, const void *data) {
  if (addr + len * sizeof(uint32_t) >= kMaxSize) {
    return kErrorFlashCtrlDataWrite;
  }
  memcpy((void *)(kBaseAddress + addr), data, len * sizeof(uint32_t));
  return kErrorOk;
}

rom_error_t ctn_sram_data_erase(uint32_t addr,
                                ctn_sram_erase_type_t erase_type) {
  static_assert(__builtin_popcount(FLASH_CTRL_PARAM_BYTES_PER_BANK) == 1,
                "Bytes per bank must be a power of two.");

  if (addr >= kMaxSize) {
    return kErrorFlashCtrlDataErase;
  }
  size_t byte_count = 0;
  switch (erase_type) {
    case kCtnSramEraseTypeBank:
      HARDENED_CHECK_EQ(erase_type, kCtnSramEraseTypeBank);
      byte_count = FLASH_CTRL_PARAM_BYTES_PER_BANK;
      break;
    case kCtnSramEraseTypePage:
      HARDENED_CHECK_EQ(erase_type, kCtnSramEraseTypePage);
      byte_count = FLASH_CTRL_PARAM_BYTES_PER_PAGE;
      break;
    default:
      HARDENED_TRAP();
      byte_count = 0U;
      break;
  }
  // Truncate to the closest lower bank/page aligned address.
  addr &= ~byte_count + 1;
  memset((void *)(kBaseAddress + addr), 0xff, byte_count);
  return kErrorOk;
}

rom_error_t ctn_sram_data_erase_verify(uint32_t addr,
                                       ctn_sram_erase_type_t erase_type) {
  static_assert(__builtin_popcount(FLASH_CTRL_PARAM_BYTES_PER_BANK) == 1,
                "Bytes per bank must be a power of two.");

  if (addr >= kMaxSize) {
    return kErrorFlashCtrlDataErase;
  }
  size_t byte_count = 0;
  rom_error_t error = kErrorFlashCtrlDataEraseVerify;
  switch (launder32(erase_type)) {
    case kCtnSramEraseTypeBank:
      HARDENED_CHECK_EQ(erase_type, kCtnSramEraseTypeBank);
      byte_count = FLASH_CTRL_PARAM_BYTES_PER_BANK;
      error = kErrorOk ^ (byte_count - 1);
      break;
    case kCtnSramEraseTypePage:
      HARDENED_CHECK_EQ(erase_type, kCtnSramEraseTypePage);
      byte_count = FLASH_CTRL_PARAM_BYTES_PER_PAGE;
      error = kErrorOk ^ (byte_count - 1);
      break;
    default:
      HARDENED_TRAP();
      byte_count = 0U;
      break;
  }

  // Truncate to the closest lower bank/page aligned address.
  addr &= ~byte_count + 1;
  uint32_t mask = kErasedWord;
  size_t i = 0, r = byte_count - 1;
  for (; launder32(i) < byte_count && launder32(r) < byte_count;
       i += sizeof(uint32_t), r -= sizeof(uint32_t)) {
    uint32_t word = abs_mmio_read32(kBaseAddress + addr + i);
    mask &= word;
    error &= word;
  }
  HARDENED_CHECK_EQ(i, byte_count);
  HARDENED_CHECK_EQ((uint32_t)r, UINT32_MAX);

  if (launder32(mask) == kErasedWord) {
    HARDENED_CHECK_EQ(mask, kErasedWord);
    return error ^ (byte_count - 1);
  }

  return kErrorFlashCtrlDataEraseVerify;
}

void ctn_sram_data_default_perms_set(ctn_sram_perms_t perms) {
  // Note: provided to maintain compatibility with flash controller
}

void ctn_sram_bank_erase_perms_set(hardened_bool_t enable) {
  // Note: provided to maintain compatibility with flash controller
}
