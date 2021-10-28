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

static_assert(kFlashCtrlRegionData == 0u,
              "Incorrect enum value for kFlashCtrlRegionData");
static_assert(kFlashCtrlRegionInfo0 ==
                  1u << FLASH_CTRL_CONTROL_PARTITION_SEL_BIT,
              "Incorrect enum value for kFlashCtrlRegionInfo0");
static_assert(kFlashCtrlRegionInfo1 ==
                  (1u << FLASH_CTRL_CONTROL_PARTITION_SEL_BIT |
                   1u << FLASH_CTRL_CONTROL_INFO_SEL_OFFSET),
              "Incorrect enum value for kFlashCtrlRegionInfo1");
static_assert(kFlashCtrlRegionInfo2 ==
                  (1u << FLASH_CTRL_CONTROL_PARTITION_SEL_BIT |
                   2u << FLASH_CTRL_CONTROL_INFO_SEL_OFFSET),
              "Incorrect enum value for kFlashCtrlRegionInfo2");
static_assert(kFlashCtrlErasePage == 0u,
              "Incorrect enum value for kFlashCtrlErasePage");
static_assert(kFlashCtrlEraseBank == 1u << FLASH_CTRL_CONTROL_ERASE_SEL_BIT,
              "Incorrect enum value for kFlashCtrlEraseBank");

enum {
  kBase = TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR,
};

static bool is_busy(void) {
  uint32_t bitfield =
      abs_mmio_read32(kBase + FLASH_CTRL_CTRL_REGWEN_REG_OFFSET);
  return !bitfield_bit32_read(bitfield, FLASH_CTRL_CTRL_REGWEN_EN_BIT);
}

static rom_error_t transaction_start(uint32_t addr, uint32_t word_count,
                                     flash_ctrl_partition_t region,
                                     flash_ctrl_erase_type_t erase_type,
                                     uint32_t op) {
  if (is_busy()) {
    return kErrorFlashCtrlBusy;
  }

  // Set the address.
  abs_mmio_write32(kBase + FLASH_CTRL_ADDR_REG_OFFSET, addr);

  // Set the operation of the transaction: read, program, or erase.
  uint32_t control_reg_val =
      bitfield_field32_write(0, FLASH_CTRL_CONTROL_OP_FIELD, op);

  // Set the partition.
  control_reg_val |= (uint32_t)region;

  // Set the erase type.
  control_reg_val |= (uint32_t)erase_type;

  // Set the number of words as `word_count - 1` as noted in #3353.
  control_reg_val = bitfield_field32_write(
      control_reg_val, FLASH_CTRL_CONTROL_NUM_FIELD, word_count - 1);

  // Start the transaction.
  control_reg_val =
      bitfield_bit32_write(control_reg_val, FLASH_CTRL_CONTROL_START_BIT, true);

  // Write the configuration.
  abs_mmio_write32(kBase + FLASH_CTRL_CONTROL_REG_OFFSET, control_reg_val);

  return kErrorOk;
}

static void fifo_read(size_t word_count, uint32_t *data_out) {
  // Keep reading until no words remain. For large reads this may create back
  // pressure.
  for (size_t words_read = 0; words_read < word_count; ++words_read) {
    data_out[words_read] =
        abs_mmio_read32(kBase + FLASH_CTRL_RD_FIFO_REG_OFFSET);
  }
}

static void fifo_push(size_t word_count, const uint32_t *data) {
  // Keep writing until no words remain. For large writes this may create back
  // pressure.
  for (size_t words_programmed = 0; words_programmed < word_count;
       ++words_programmed) {
    abs_mmio_write32(kBase + FLASH_CTRL_PROG_FIFO_REG_OFFSET,
                     data[words_programmed]);
  }
}

static rom_error_t check_errors(void) {
  uint32_t op_status = abs_mmio_read32(kBase + FLASH_CTRL_OP_STATUS_REG_OFFSET);
  if (bitfield_bit32_read(op_status, FLASH_CTRL_OP_STATUS_ERR_BIT)) {
    return kErrorFlashCtrlInternal;
  }
  return kErrorOk;
}

static rom_error_t wait_for_done(void) {
  uint32_t op_status;
  do {
    op_status = abs_mmio_read32(kBase + FLASH_CTRL_OP_STATUS_REG_OFFSET);
  } while (!bitfield_bit32_read(op_status, FLASH_CTRL_OP_STATUS_DONE_BIT));

  rom_error_t res = check_errors();

  // Clear OP_STATUS.
  abs_mmio_write32(kBase + FLASH_CTRL_OP_STATUS_REG_OFFSET, 0u);

  return res;
}

void flash_ctrl_init(void) {
  // Initialize the flash controller.
  abs_mmio_write32(kBase + FLASH_CTRL_INIT_REG_OFFSET,
                   bitfield_bit32_write(0u, FLASH_CTRL_INIT_VAL_BIT, true));
}

void flash_ctrl_status_get(flash_ctrl_status_t *status) {
  // Read flash controller status.
  uint32_t fc_status = abs_mmio_read32(kBase + FLASH_CTRL_STATUS_REG_OFFSET);

  // Extract flash controller status bits.
  status->rd_full =
      bitfield_bit32_read(fc_status, FLASH_CTRL_STATUS_RD_FULL_BIT);
  status->rd_empty =
      bitfield_bit32_read(fc_status, FLASH_CTRL_STATUS_RD_EMPTY_BIT);
  status->prog_full =
      bitfield_bit32_read(fc_status, FLASH_CTRL_STATUS_PROG_FULL_BIT);
  status->prog_empty =
      bitfield_bit32_read(fc_status, FLASH_CTRL_STATUS_PROG_EMPTY_BIT);
  status->init_wip =
      bitfield_bit32_read(fc_status, FLASH_CTRL_STATUS_INIT_WIP_BIT);
}

rom_error_t flash_ctrl_read(uint32_t addr, uint32_t word_count,
                            flash_ctrl_partition_t region, uint32_t *data) {
  // Start the read transaction, the value of `erase_type` doesn't matter.
  RETURN_IF_ERROR(transaction_start(addr, word_count, region,
                                    kFlashCtrlErasePage,
                                    FLASH_CTRL_CONTROL_OP_VALUE_READ));
  fifo_read(word_count, data);
  return wait_for_done();
}

rom_error_t flash_ctrl_prog(uint32_t addr, uint32_t word_count,
                            flash_ctrl_partition_t region,
                            const uint32_t *data) {
  uint32_t window_offset = addr % FLASH_CTRL_PARAM_REG_BUS_PGM_RES_BYTES;

  while (word_count > 0) {
    // Program operations can't cross window boundaries.
    uint32_t max_bytes = FLASH_CTRL_PARAM_REG_BUS_PGM_RES_BYTES - window_offset;
    uint32_t write_size = max_bytes / sizeof(uint32_t);
    write_size = word_count < write_size ? word_count : write_size;
    window_offset = 0;

    // Start the program transaction, the value of `erase_type` doesn't matter.
    RETURN_IF_ERROR(transaction_start(addr, write_size, region,
                                      kFlashCtrlErasePage,
                                      FLASH_CTRL_CONTROL_OP_VALUE_PROG));

    fifo_push(write_size, data);
    RETURN_IF_ERROR(wait_for_done());

    addr += write_size * sizeof(uint32_t);
    data += write_size;
    word_count -= write_size;
  }

  return kErrorOk;
}

rom_error_t flash_ctrl_erase(uint32_t addr, flash_ctrl_partition_t region,
                             flash_ctrl_erase_type_t type) {
  // Start the erase transaction, the value of `word_count` doesn't matter.
  RETURN_IF_ERROR(transaction_start(addr, 1u, region, type,
                                    FLASH_CTRL_CONTROL_OP_VALUE_ERASE));

  return wait_for_done();
}

void flash_ctrl_exec_set(flash_ctrl_exec_t enable) {
  // Enable or disable flash execution.
  abs_mmio_write32(kBase + FLASH_CTRL_EXEC_REG_OFFSET, (uint32_t)enable);
}
