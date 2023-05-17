// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/otbn.h"

#include <assert.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/rnd.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otbn_regs.h"  // Generated.

enum {
  /**
   * Base address for OTBN.
   */
  kBase = TOP_EARLGREY_OTBN_BASE_ADDR,
  /**
   * Highest index of OTBN error bits.
   */
  kOtbnErrBitsLast = OTBN_ERR_BITS_FATAL_SOFTWARE_BIT,
};

/**
 * Ensures that `offset_bytes` and `len` are valid for a given `mem_size`.
 */
static rom_error_t check_offset_len(uint32_t offset_bytes, size_t num_words,
                                    size_t mem_size) {
  if (num_words > UINT32_MAX / sizeof(uint32_t)) {
    return kErrorOtbnBadOffsetLen;
  }
  uint32_t num_bytes = num_words * sizeof(uint32_t);

  if (offset_bytes > UINT32_MAX - num_bytes) {
    return kErrorOtbnBadOffsetLen;
  }
  uint32_t adjusted_offset_bytes = offset_bytes + num_bytes;

  if (adjusted_offset_bytes > mem_size) {
    return kErrorOtbnBadOffsetLen;
  }

  return kErrorOk;
}

rom_error_t otbn_busy_wait_for_done(void) {
  uint32_t status = launder32(UINT32_MAX);
  rom_error_t res = launder32(kErrorOk ^ status);
  do {
    status = abs_mmio_read32(kBase + OTBN_STATUS_REG_OFFSET);
  } while (launder32(status) != kOtbnStatusIdle &&
           launder32(status) != kOtbnStatusLocked);
  res ^= ~status;
  if (launder32(res) == kErrorOk) {
    HARDENED_CHECK_EQ(res, kErrorOk);
    HARDENED_CHECK_EQ(abs_mmio_read32(kBase + OTBN_STATUS_REG_OFFSET),
                      kOtbnStatusIdle);
    return res;
  }
  return kErrorOtbnUnavailable;
}

/**
 * Helper function for writing to OTBN's DMEM or IMEM.
 *
 * @param dest_addr Destination address.
 * @param src Source buffer.
 * @param num_words Number of words to copy.
 */
static void otbn_write(uint32_t dest_addr, const uint32_t *src,
                       size_t num_words) {
  // Start from a random index less than `num_words`.
  size_t i = ((uint64_t)rnd_uint32() * (uint64_t)num_words) >> 32;
  enum { kStep = 1 };
  size_t iter_cnt = 0, r_iter_cnt = num_words - 1;
  for (; launder32(iter_cnt) < num_words && launder32(r_iter_cnt) < num_words;
       ++iter_cnt, --r_iter_cnt) {
    abs_mmio_write32(dest_addr + i * sizeof(uint32_t), src[i]);
    i += kStep;
    if (launder32(i) >= num_words) {
      i -= num_words;
    }
    HARDENED_CHECK_LT(i, num_words);
  }
  HARDENED_CHECK_EQ(iter_cnt, num_words);
  HARDENED_CHECK_EQ((uint32_t)r_iter_cnt, UINT32_MAX);
}

static rom_error_t otbn_imem_write(size_t num_words, const uint32_t *src,
                                   otbn_addr_t dest) {
  HARDENED_RETURN_IF_ERROR(
      check_offset_len(dest, num_words, OTBN_IMEM_SIZE_BYTES));
  otbn_write(kBase + OTBN_IMEM_REG_OFFSET + dest, src, num_words);
  return kErrorOk;
}

rom_error_t otbn_dmem_write(size_t num_words, const uint32_t *src,
                            otbn_addr_t dest) {
  HARDENED_RETURN_IF_ERROR(
      check_offset_len(dest, num_words, OTBN_DMEM_SIZE_BYTES));
  otbn_write(kBase + OTBN_DMEM_REG_OFFSET + dest, src, num_words);
  return kErrorOk;
}

rom_error_t otbn_dmem_read(size_t num_words, otbn_addr_t src, uint32_t *dest) {
  HARDENED_RETURN_IF_ERROR(
      check_offset_len(src, num_words, OTBN_DMEM_SIZE_BYTES));
  size_t i = 0, r = num_words - 1;
  for (; launder32(i) < num_words && launder32(r) < num_words; ++i, --r) {
    dest[i] = abs_mmio_read32(kBase + OTBN_DMEM_REG_OFFSET + src +
                              i * sizeof(uint32_t));
  }
  HARDENED_CHECK_EQ(i, num_words);
  HARDENED_CHECK_EQ((uint32_t)r, UINT32_MAX);
  return kErrorOk;
}

/**
 * Helper function for running an OTBN command.
 *
 * This function blocks until OTBN is idle.
 *
 * @param cmd OTBN command.
 * @param error Error to return if operation fails.
 * @return Result of the operation.
 */
static rom_error_t otbn_cmd_run(otbn_cmd_t cmd, rom_error_t error) {
  enum {
    kIntrStateDone = (1 << OTBN_INTR_COMMON_DONE_BIT),
    // Use a bit index that doesn't overlap with error bits.
    kResDoneBit = 31,
  };
  static_assert((UINT32_C(1) << kResDoneBit) > kOtbnErrBitsLast,
                "kResDoneBit must not overlap with OTBN error bits");

  abs_mmio_write32(kBase + OTBN_INTR_STATE_REG_OFFSET, kIntrStateDone);
  abs_mmio_write32(kBase + OTBN_CMD_REG_OFFSET, cmd);

  rom_error_t res = kErrorOk ^ (UINT32_C(1) << kResDoneBit);
  uint32_t reg = 0;
  do {
    reg = abs_mmio_read32(kBase + OTBN_INTR_STATE_REG_OFFSET);
    res ^= (uint32_t)bitfield_bit32_read(reg, OTBN_INTR_COMMON_DONE_BIT)
           << kResDoneBit;
  } while (launder32(reg) != kIntrStateDone);
  HARDENED_CHECK_EQ(reg, kIntrStateDone);
  abs_mmio_write32(kBase + OTBN_INTR_STATE_REG_OFFSET, kIntrStateDone);

  // Error bits register should be 0 (no errors).
  uint32_t err_bits = abs_mmio_read32(kBase + OTBN_ERR_BITS_REG_OFFSET);
  res ^= err_bits;

  // Status should be kOtbnStatusIdle; OTBN can also issue a done interrupt
  // when transitioning to the "locked" state, so it is important to check
  // the status here.
  uint32_t status = abs_mmio_read32(kBase + OTBN_STATUS_REG_OFFSET);

  if (launder32(res) == kErrorOk && launder32(err_bits) == 0 &&
      launder32(status) == kOtbnStatusIdle) {
    HARDENED_CHECK_EQ(res, kErrorOk);
    HARDENED_CHECK_EQ(err_bits, 0);
    HARDENED_CHECK_EQ(abs_mmio_read32(kBase + OTBN_STATUS_REG_OFFSET),
                      kOtbnStatusIdle);
    return res;
  }
  return error;
}

rom_error_t otbn_execute(void) {
  // If OTBN is busy, wait for it to be done.
  HARDENED_RETURN_IF_ERROR(otbn_busy_wait_for_done());

  // Set software errors to fatal before running the program. Note: the CTRL
  // register has only this one setting, so we have no need to read the
  // previous value.
  sec_mmio_write32(kBase + OTBN_CTRL_REG_OFFSET,
                   1 << OTBN_CTRL_SOFTWARE_ERRS_FATAL_BIT);

  return otbn_cmd_run(kOtbnCmdExecute, kErrorOtbnExecutionFailed);
}

uint32_t otbn_instruction_count_get(void) {
  return abs_mmio_read32(kBase + OTBN_INSN_CNT_REG_OFFSET);
}

rom_error_t otbn_imem_sec_wipe(void) {
  return otbn_cmd_run(kOtbnCmdSecWipeImem, kErrorOtbnSecWipeImemFailed);
}

rom_error_t otbn_dmem_sec_wipe(void) {
  return otbn_cmd_run(kOtbnCmdSecWipeDmem, kErrorOtbnSecWipeDmemFailed);
}

/**
 * Checks if the OTBN application's IMEM and DMEM address parameters are valid.
 *
 * IMEM and DMEM ranges must not be "backwards" in memory, with the end address
 * coming before the start address, and the IMEM range must additionally be
 * non-empty.
 *
 * @param app the OTBN application to check
 * @return OK if the addresses are valid, otherwise `kErrorOtbnInvalidArgument`.
 */
static rom_error_t check_app_address_ranges(const otbn_app_t app) {
  if (app.imem_end > app.imem_start &&
      app.dmem_data_end >= app.dmem_data_start) {
    HARDENED_CHECK_GT(app.imem_end, app.imem_start);
    HARDENED_CHECK_GE(app.dmem_data_end, app.dmem_data_start);
    return kErrorOk;
  }
  return kErrorOtbnInvalidArgument;
}

rom_error_t otbn_load_app(const otbn_app_t app) {
  HARDENED_RETURN_IF_ERROR(check_app_address_ranges(app));

  // If OTBN is busy, wait for it to be done.
  HARDENED_RETURN_IF_ERROR(otbn_busy_wait_for_done());

  // Wipe memories.
  HARDENED_RETURN_IF_ERROR(otbn_dmem_sec_wipe());
  HARDENED_RETURN_IF_ERROR(otbn_imem_sec_wipe());

  const size_t imem_num_words = (size_t)(app.imem_end - app.imem_start);
  const size_t data_num_words =
      (size_t)(app.dmem_data_end - app.dmem_data_start);

  // IMEM always starts at 0.
  otbn_addr_t imem_start_addr = 0;
  HARDENED_RETURN_IF_ERROR(
      otbn_imem_write(imem_num_words, app.imem_start, imem_start_addr));

  if (data_num_words > 0) {
    HARDENED_RETURN_IF_ERROR(otbn_dmem_write(
        data_num_words, app.dmem_data_start, app.dmem_data_start_addr));
  }
  return kErrorOk;
}
