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

// Values of `flash_ctrl_partition_t` constants must be distinct from each
// other, and `kFlashCtrlRegionInfo* >> 1` should give the correct
// CONTROL.INFO_SEL value.
static_assert(kFlashCtrlPartitionData == 0u,
              "Incorrect enum value for kFlashCtrlRegionData");
static_assert(kFlashCtrlPartitionInfo0 >> 1 == 0,
              "Incorrect enum value for kFlashCtrlRegionInfo0");
static_assert(kFlashCtrlPartitionInfo1 >> 1 == 1,
              "Incorrect enum value for kFlashCtrlRegionInfo1");
static_assert(kFlashCtrlPartitionInfo2 >> 1 == 2,
              "Incorrect enum value for kFlashCtrlRegionInfo2");

enum {
  kBase = TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR,
};

static bool is_busy(void) {
  uint32_t bitfield =
      abs_mmio_read32(kBase + FLASH_CTRL_CTRL_REGWEN_REG_OFFSET);
  return !bitfield_bit32_read(bitfield, FLASH_CTRL_CTRL_REGWEN_EN_BIT);
}

/**
 * Flash transaction parameters.
 */
typedef struct transaction_params {
  /**
   * Start address of a flash transaction.
   *
   * Must be the full byte address. For read and write operations flash
   * controller will truncate to the closest 32-bit word aligned address. For
   * page erases, the controller will truncate to the closest lower page aligned
   * address. For bank erases, the controller will truncate to the closest lower
   * bank aligned address.
   */
  uint32_t addr;
  /**
   * Operation type.
   *
   * Must be set to one of FLASH_CTRL_CONTROL_OP_VALUE_*.
   */
  uint32_t op_type;
  /**
   * Whether to erase a bank or a single page.
   *
   * Only applies to erase operations.
   */
  flash_ctrl_erase_type_t erase_type;
  /**
   * Partition to operate on.
   */
  flash_ctrl_partition_t partition;
  /**
   * Number of 32-bit words.
   *
   * Only applies to read and write operations.
   */
  uint32_t word_count;
} transaction_params_t;

/**
 * Starts a flash transaction.
 *
 * @param params Transaction parameters, see `transaction_params_t`.
 * @return The result of the operation.
 */
static rom_error_t transaction_start(transaction_params_t params) {
  if (is_busy()) {
    return kErrorFlashCtrlBusy;
  }

  // Set the address.
  abs_mmio_write32(kBase + FLASH_CTRL_ADDR_REG_OFFSET, params.addr);
  // Configure flash_ctrl and start the transaction.
  uint32_t reg = bitfield_bit32_write(0, FLASH_CTRL_CONTROL_START_BIT, true);
  reg =
      bitfield_field32_write(reg, FLASH_CTRL_CONTROL_OP_FIELD, params.op_type);
  reg = bitfield_bit32_write(reg, FLASH_CTRL_CONTROL_PARTITION_SEL_BIT,
                             params.partition != kFlashCtrlPartitionData);
  reg = bitfield_field32_write(reg, FLASH_CTRL_CONTROL_INFO_SEL_FIELD,
                               (uint32_t)params.partition >> 1);
  reg = bitfield_bit32_write(reg, FLASH_CTRL_CONTROL_ERASE_SEL_BIT,
                             params.erase_type == kFlashCtrlEraseTypeBank);
  // TODO(#3353): Remove -1 when flash_ctrl is updated.
  reg = bitfield_field32_write(reg, FLASH_CTRL_CONTROL_NUM_FIELD,
                               params.word_count - 1);
  abs_mmio_write32(kBase + FLASH_CTRL_CONTROL_REG_OFFSET, reg);
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

/**
 * Blocks until the current flash transaction is complete.
 *
 * @return The result of the operation.
 */
static rom_error_t wait_for_done(void) {
  uint32_t op_status;
  do {
    op_status = abs_mmio_read32(kBase + FLASH_CTRL_OP_STATUS_REG_OFFSET);
  } while (!bitfield_bit32_read(op_status, FLASH_CTRL_OP_STATUS_DONE_BIT));
  abs_mmio_write32(kBase + FLASH_CTRL_OP_STATUS_REG_OFFSET, 0u);

  if (bitfield_bit32_read(op_status, FLASH_CTRL_OP_STATUS_ERR_BIT)) {
    return kErrorFlashCtrlInternal;
  }
  return kErrorOk;
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
                            flash_ctrl_partition_t partition, uint32_t *data) {
  RETURN_IF_ERROR(transaction_start((transaction_params_t){
      .addr = addr,
      .op_type = FLASH_CTRL_CONTROL_OP_VALUE_READ,
      .partition = partition,
      .word_count = word_count,
      // Does not apply to read transactions.
      .erase_type = kFlashCtrlEraseTypePage,
  }));
  fifo_read(word_count, data);
  return wait_for_done();
}

rom_error_t flash_ctrl_prog(uint32_t addr, uint32_t word_count,
                            flash_ctrl_partition_t partition,
                            const uint32_t *data) {
  uint32_t window_offset = addr % FLASH_CTRL_PARAM_REG_BUS_PGM_RES_BYTES;

  while (word_count > 0) {
    // Program operations can't cross window boundaries.
    uint32_t max_bytes = FLASH_CTRL_PARAM_REG_BUS_PGM_RES_BYTES - window_offset;
    uint32_t write_size = max_bytes / sizeof(uint32_t);
    write_size = word_count < write_size ? word_count : write_size;
    window_offset = 0;

    RETURN_IF_ERROR(transaction_start((transaction_params_t){
        .addr = addr,
        .op_type = FLASH_CTRL_CONTROL_OP_VALUE_PROG,
        .partition = partition,
        .word_count = write_size,
        // Does not apply to program transactions.
        .erase_type = kFlashCtrlEraseTypePage,
    }));

    fifo_push(write_size, data);
    RETURN_IF_ERROR(wait_for_done());

    addr += write_size * sizeof(uint32_t);
    data += write_size;
    word_count -= write_size;
  }

  return kErrorOk;
}

rom_error_t flash_ctrl_erase(uint32_t addr, flash_ctrl_partition_t partition,
                             flash_ctrl_erase_type_t erase_type) {
  RETURN_IF_ERROR(transaction_start((transaction_params_t){
      .addr = addr,
      .op_type = FLASH_CTRL_CONTROL_OP_VALUE_ERASE,
      .erase_type = erase_type,
      .partition = partition,
      // Does not apply to erase transactions.
      .word_count = 1,
  }));

  return wait_for_done();
}

void flash_ctrl_exec_set(flash_ctrl_exec_t enable) {
  // Enable or disable flash execution.
  abs_mmio_write32(kBase + FLASH_CTRL_EXEC_REG_OFFSET, (uint32_t)enable);
}
