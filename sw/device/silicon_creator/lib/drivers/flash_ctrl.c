// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"

#include <assert.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/silicon_creator/lib/base/abs_mmio.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "flash_ctrl_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

enum {
  kBase = TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR,
};

static bool is_busy(void) {
  uint32_t bitfield =
      abs_mmio_read32(kBase + FLASH_CTRL_CTRL_REGWEN_REG_OFFSET);
  return !bitfield_bit32_read(bitfield, FLASH_CTRL_CTRL_REGWEN_EN_BIT);
}

void flash_ctrl_init(void) {
  // Initialize the flash controller.
  abs_mmio_write32(kBase + FLASH_CTRL_INIT_REG_OFFSET,
                   bitfield_bit32_write(0u, FLASH_CTRL_INIT_VAL_BIT, true));
}

rom_error_t flash_ctrl_status_get(flash_ctrl_status_t *status) {
  if (status == NULL) {
    return kErrorFlashCtrlInvalidArgument;
  }

  // Read flash operation status.
  uint32_t op_status = abs_mmio_read32(kBase + FLASH_CTRL_OP_STATUS_REG_OFFSET);
  // Read flash controller status.
  uint32_t fc_status = abs_mmio_read32(kBase + FLASH_CTRL_STATUS_REG_OFFSET);

  // Extract operation status bits.
  status->done = bitfield_bit32_read(op_status, FLASH_CTRL_OP_STATUS_DONE_BIT);
  status->err = bitfield_bit32_read(op_status, FLASH_CTRL_OP_STATUS_ERR_BIT);

  // Extract flash controller status bits.
  status->rd_full =
      bitfield_bit32_read(fc_status, FLASH_CTRL_STATUS_RD_FULL_BIT);
  status->rd_empty =
      bitfield_bit32_read(fc_status, FLASH_CTRL_STATUS_RD_EMPTY_BIT);
  status->init_wip =
      bitfield_bit32_read(fc_status, FLASH_CTRL_STATUS_INIT_WIP_BIT);

  return kErrorOk;
}

rom_error_t flash_ctrl_read_start(uint32_t addr, uint32_t word_count,
                                  flash_ctrl_partition_t region) {
  if (is_busy()) {
    return kErrorFlashCtrlBusy;
  }

  // Set the address.
  abs_mmio_write32(kBase + FLASH_CTRL_ADDR_REG_OFFSET, addr);

  // Set the operation of the transaction: read, program, or erase.
  uint32_t control_reg_val = bitfield_field32_write(
      0, FLASH_CTRL_CONTROL_OP_FIELD, FLASH_CTRL_CONTROL_OP_VALUE_READ);

  // Ensure special enum values match register definitions.
  static_assert(kFlashCtrlRegionData == 0u,
                "Incorrect enum value for kFlashCtrlRegionData");
  static_assert(
      kFlashCtrlRegionInfo0 == 1u << FLASH_CTRL_CONTROL_PARTITION_SEL_BIT,
      "Incorrect enum value for kFlashCtrlRegionInfo0");
  static_assert(
      kFlashCtrlRegionInfo1 == (1u << FLASH_CTRL_CONTROL_PARTITION_SEL_BIT |
                                1u << FLASH_CTRL_CONTROL_INFO_SEL_OFFSET),
      "Incorrect enum value for kFlashCtrlRegionInfo1");
  static_assert(
      kFlashCtrlRegionInfo2 == (1u << FLASH_CTRL_CONTROL_PARTITION_SEL_BIT |
                                2u << FLASH_CTRL_CONTROL_INFO_SEL_OFFSET),
      "Incorrect enum value for kFlashCtrlRegionInfo2");

  // Set the partition.
  control_reg_val |= (uint32_t)region;

  // Set the number of words.
  control_reg_val = bitfield_field32_write(
      control_reg_val, FLASH_CTRL_CONTROL_NUM_FIELD, word_count);

  // Start the transaction.
  control_reg_val =
      bitfield_bit32_write(control_reg_val, FLASH_CTRL_CONTROL_START_BIT, true);

  // Write the configuration.
  abs_mmio_write32(kBase + FLASH_CTRL_CONTROL_REG_OFFSET, control_reg_val);

  return kErrorOk;
}

size_t flash_ctrl_fifo_read(size_t word_count, uint32_t *data_out) {
  // Keep reading until no words remain. For large reads this may create back
  // pressure.
  size_t words_read = 0;
  for (; words_read < word_count; ++words_read) {
    data_out[words_read] =
        abs_mmio_read32(kBase + FLASH_CTRL_RD_FIFO_REG_OFFSET);
  }

  return words_read;
}

void flash_ctrl_exec_set(flash_ctrl_exec_t enable) {
  // Enable or disable flash execution.
  abs_mmio_write32(kBase + FLASH_CTRL_EXEC_REG_OFFSET, (uint32_t)enable);
}
