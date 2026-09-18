// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/otbn.h"

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "hw/top/dt/otbn.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/crc32.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/rnd.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "hw/top/otbn_regs.h"  // Generated.

static inline uint32_t otbn_base(void) {
  return dt_otbn_primary_reg_block(kDtOtbn);
}

enum {
  /**
   * Highest index of OTBN error bits.
   */
  kOtbnErrBitsLast = OTBN_ERR_BITS_FATAL_SOFTWARE_BIT,
  kIntrStateDone = (1 << OTBN_INTR_COMMON_DONE_BIT),
};

/**
 * Ensures that `offset_bytes` and `len` are valid for a given `mem_size`.
 */
OT_WARN_UNUSED_RESULT
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

rom_error_t sc_otbn_busy_wait_for_done(void) {
  uint32_t status = launder32(UINT32_MAX);
  rom_error_t res = launder32(kErrorOk ^ status);
  do {
    status = abs_mmio_read32(otbn_base() + OTBN_STATUS_REG_OFFSET);
  } while (launder32(status) != kScOtbnStatusIdle &&
           launder32(status) != kScOtbnStatusLocked);
  res ^= ~status;
  if (launder32(res) == kErrorOk) {
    HARDENED_CHECK_EQ(res, kErrorOk);
    HARDENED_CHECK_EQ(abs_mmio_read32(otbn_base() + OTBN_STATUS_REG_OFFSET),
                      kScOtbnStatusIdle);
    return res;
  }
  return kErrorOtbnUnavailable;
}

/**
 * Helper function for writing public data linearly to OTBN's DMEM or IMEM with
 * LOAD_CHECKSUM verification.
 *
 * @param dest_reg_offset Base register offset (OTBN_IMEM_REG_OFFSET or
 * OTBN_DMEM_REG_OFFSET).
 * @param is_imem True for IMEM writes, false for DMEM writes.
 * @param dest Destination address in OTBN memory.
 * @param src Source buffer.
 * @param num_words Number of words to copy.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t sc_otbn_write_public(uint32_t dest_reg_offset, bool is_imem,
                                        sc_otbn_addr_t dest,
                                        const uint32_t *src, size_t num_words) {
  const uint32_t kBase = otbn_base();
  abs_mmio_write32(kBase + OTBN_LOAD_CHECKSUM_REG_OFFSET, 0);

  uint32_t ctx;
  crc32_init(&ctx);

  uint32_t i = 0, r = num_words - 1;
  for (; launder32(i) < num_words && launder32(r) < num_words; ++i, --r) {
    size_t idx_word = i * sizeof(uint32_t);
    abs_mmio_write32(kBase + dest_reg_offset + dest + idx_word, src[i]);

    uint32_t offset =
        (((dest + idx_word) >> 2) & 0x7FFF) | (is_imem ? (1 << 15) : 0);
    crc32_add32(&ctx, src[i]);
    crc32_add8(&ctx, (uint8_t)offset);
    crc32_add8(&ctx, (uint8_t)(offset >> 8));
  }
  HARDENED_CHECK_EQ(i, num_words);
  HARDENED_CHECK_EQ(r, UINT32_MAX);

  uint32_t checksum_expected = crc32_finish(&ctx);
  uint32_t checksum = abs_mmio_read32(kBase + OTBN_LOAD_CHECKSUM_REG_OFFSET);
  if (launder32(checksum) != checksum_expected) {
    return kErrorOtbnBadChecksum;
  }
  HARDENED_CHECK_EQ(checksum, checksum_expected);
  return kErrorOk;
}

OT_WARN_UNUSED_RESULT
static rom_error_t sc_otbn_imem_write(size_t num_words, const uint32_t *src,
                                      sc_otbn_addr_t dest) {
  HARDENED_RETURN_IF_ERROR(
      check_offset_len(dest, num_words, OTBN_IMEM_SIZE_BYTES));
  return sc_otbn_write_public(OTBN_IMEM_REG_OFFSET, /*is_imem=*/true, dest, src,
                              num_words);
}

rom_error_t sc_otbn_dmem_write(size_t num_words, const uint32_t *src,
                               sc_otbn_addr_t dest) {
  HARDENED_RETURN_IF_ERROR(
      check_offset_len(dest, num_words, OTBN_DMEM_SIZE_BYTES));
  const uint32_t kBase = otbn_base();
  abs_mmio_write32(kBase + OTBN_LOAD_CHECKSUM_REG_OFFSET, 0);

  uint32_t ctx;
  crc32_init(&ctx);

  // Start from a random index less than `num_words`.
  uint32_t i = ((uint64_t)rnd_uint32() * (uint64_t)num_words) >> 32;
  uint32_t iter_cnt = 0, r_iter_cnt = num_words - 1;
  for (; launder32(iter_cnt) < num_words && launder32(r_iter_cnt) < num_words;
       ++iter_cnt, --r_iter_cnt) {
    size_t idx_word = i * sizeof(uint32_t);
    abs_mmio_write32(kBase + OTBN_DMEM_REG_OFFSET + dest + idx_word, src[i]);

    uint32_t offset = ((dest + idx_word) >> 2) & 0x7FFF;
    crc32_add32(&ctx, src[i]);
    crc32_add8(&ctx, (uint8_t)offset);
    crc32_add8(&ctx, (uint8_t)(offset >> 8));

    ++i;
    if (launder32(i) >= num_words) {
      i -= num_words;
    }
    HARDENED_CHECK_LT(i, num_words);
  }
  HARDENED_CHECK_EQ(iter_cnt, num_words);
  HARDENED_CHECK_EQ(r_iter_cnt, UINT32_MAX);

  uint32_t checksum_expected = crc32_finish(&ctx);
  uint32_t checksum = abs_mmio_read32(kBase + OTBN_LOAD_CHECKSUM_REG_OFFSET);
  if (launder32(checksum) != checksum_expected) {
    return kErrorOtbnBadChecksum;
  }
  HARDENED_CHECK_EQ(checksum, checksum_expected);
  return kErrorOk;
}

rom_error_t sc_otbn_dmem_write_public(size_t num_words, const uint32_t *src,
                                      sc_otbn_addr_t dest) {
  HARDENED_RETURN_IF_ERROR(
      check_offset_len(dest, num_words, OTBN_DMEM_SIZE_BYTES));
  return sc_otbn_write_public(OTBN_DMEM_REG_OFFSET, /*is_imem=*/false, dest,
                              src, num_words);
}

rom_error_t sc_otbn_dmem_read(size_t num_words, sc_otbn_addr_t src,
                              uint32_t *dest) {
  HARDENED_RETURN_IF_ERROR(
      check_offset_len(src, num_words, OTBN_DMEM_SIZE_BYTES));
  uint32_t i = 0, r = num_words - 1;
  for (; launder32(i) < num_words && launder32(r) < num_words; ++i, --r) {
    dest[i] = abs_mmio_read32(otbn_base() + OTBN_DMEM_REG_OFFSET + src +
                              i * sizeof(uint32_t));
  }
  HARDENED_CHECK_EQ(i, num_words);
  HARDENED_CHECK_EQ(r, UINT32_MAX);
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
static void sc_otbn_cmd_start(sc_otbn_cmd_t cmd) {
  abs_mmio_write32(otbn_base() + OTBN_INTR_STATE_REG_OFFSET, kIntrStateDone);
  abs_mmio_write32(otbn_base() + OTBN_CMD_REG_OFFSET, cmd);
}

OT_WARN_UNUSED_RESULT
static rom_error_t sc_otbn_cmd_finish(rom_error_t error) {
  enum {
    // Use a bit index that doesn't overlap with error bits.
    kResDoneBit = 31,
  };
  static_assert((UINT32_C(1) << kResDoneBit) > kOtbnErrBitsLast,
                "kResDoneBit must not overlap with OTBN error bits");
  rom_error_t res = kErrorOk ^ (UINT32_C(1) << kResDoneBit);
  uint32_t reg = 0;
  do {
    reg = abs_mmio_read32(otbn_base() + OTBN_INTR_STATE_REG_OFFSET);
    res ^= (uint32_t)bitfield_bit32_read(reg, OTBN_INTR_COMMON_DONE_BIT)
           << kResDoneBit;
  } while (launder32(reg) != kIntrStateDone);
  HARDENED_CHECK_EQ(reg, kIntrStateDone);
  abs_mmio_write32(otbn_base() + OTBN_INTR_STATE_REG_OFFSET, kIntrStateDone);

  // Error bits register should be 0 (no errors).
  uint32_t err_bits = abs_mmio_read32(otbn_base() + OTBN_ERR_BITS_REG_OFFSET);
  res ^= err_bits;

  // Status should be kScOtbnStatusIdle; OTBN can also issue a done interrupt
  // when transitioning to the "locked" state, so it is important to check
  // the status here.
  uint32_t status = abs_mmio_read32(otbn_base() + OTBN_STATUS_REG_OFFSET);

  if (launder32(res) == kErrorOk && launder32(err_bits) == 0 &&
      launder32(status) == kScOtbnStatusIdle) {
    HARDENED_CHECK_EQ(res, kErrorOk);
    HARDENED_CHECK_EQ(err_bits, 0);
    HARDENED_CHECK_EQ(abs_mmio_read32(otbn_base() + OTBN_STATUS_REG_OFFSET),
                      kScOtbnStatusIdle);
    return res;
  }
  return error;
}

static rom_error_t sc_otbn_cmd_run(sc_otbn_cmd_t cmd, rom_error_t error) {
  sc_otbn_cmd_start(cmd);
  return sc_otbn_cmd_finish(error);
}

rom_error_t sc_otbn_execute_start(void) {
  // If OTBN is busy, wait for it to be done.
  HARDENED_RETURN_IF_ERROR(sc_otbn_busy_wait_for_done());

  // Set software errors to fatal before running the program. Note: the CTRL
  // register has only this one setting, so we have no need to read the
  // previous value.
  sec_mmio_write32(otbn_base() + OTBN_CTRL_REG_OFFSET,
                   1 << OTBN_CTRL_SOFTWARE_ERRS_FATAL_BIT);

  sc_otbn_cmd_start(kScOtbnCmdExecute);
  return kErrorOk;
}

rom_error_t sc_otbn_execute_finish(void) {
  return sc_otbn_cmd_finish(kErrorOtbnExecutionFailed);
}

rom_error_t sc_otbn_execute(void) {
  HARDENED_RETURN_IF_ERROR(sc_otbn_execute_start());
  return sc_otbn_execute_finish();
}

uint32_t sc_otbn_instruction_count_get(void) {
  return abs_mmio_read32(otbn_base() + OTBN_INSN_CNT_REG_OFFSET);
}

rom_error_t sc_otbn_imem_sec_wipe(void) {
  return sc_otbn_cmd_run(kScOtbnCmdSecWipeImem, kErrorOtbnSecWipeImemFailed);
}

rom_error_t sc_otbn_dmem_sec_wipe(void) {
  return sc_otbn_cmd_run(kScOtbnCmdSecWipeDmem, kErrorOtbnSecWipeDmemFailed);
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
OT_WARN_UNUSED_RESULT
static rom_error_t check_app_address_ranges(const sc_otbn_app_t app) {
  if (app.imem_end > app.imem_start &&
      app.dmem_data_end >= app.dmem_data_start) {
    HARDENED_CHECK_GT(app.imem_end, app.imem_start);
    HARDENED_CHECK_GE(app.dmem_data_end, app.dmem_data_start);
    return kErrorOk;
  }
  return kErrorOtbnInvalidArgument;
}

rom_error_t sc_otbn_load_app(const sc_otbn_app_t app) {
  HARDENED_RETURN_IF_ERROR(check_app_address_ranges(app));

  // If OTBN is busy, wait for it to be done.
  HARDENED_RETURN_IF_ERROR(sc_otbn_busy_wait_for_done());

  // Wipe memories.
  HARDENED_RETURN_IF_ERROR(sc_otbn_dmem_sec_wipe());
  HARDENED_RETURN_IF_ERROR(sc_otbn_imem_sec_wipe());

  const size_t imem_num_words = (size_t)(app.imem_end - app.imem_start);
  const size_t data_num_words =
      (size_t)(app.dmem_data_end - app.dmem_data_start);

  // IMEM always starts at 0.
  sc_otbn_addr_t imem_start_addr = 0;
  HARDENED_RETURN_IF_ERROR(
      sc_otbn_imem_write(imem_num_words, app.imem_start, imem_start_addr));

  if (data_num_words > 0) {
    HARDENED_RETURN_IF_ERROR(sc_otbn_dmem_write_public(
        data_num_words, app.dmem_data_start, app.dmem_data_start_addr));
  }
  return kErrorOk;
}
