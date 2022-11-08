// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/otbn.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/hardened.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otbn_regs.h"  // Generated.

#define ASSERT_ERR_BIT_MATCH(enum_val, autogen_val) \
  static_assert(enum_val == 1 << (autogen_val),     \
                "OTBN register bit doesn't match autogen value.");

ASSERT_ERR_BIT_MATCH(kOtbnErrBitsBadDataAddr, OTBN_ERR_BITS_BAD_DATA_ADDR_BIT);
ASSERT_ERR_BIT_MATCH(kOtbnErrBitsBadInsnAddr, OTBN_ERR_BITS_BAD_INSN_ADDR_BIT);
ASSERT_ERR_BIT_MATCH(kOtbnErrBitsCallStack, OTBN_ERR_BITS_CALL_STACK_BIT);
ASSERT_ERR_BIT_MATCH(kOtbnErrBitsIllegalInsn, OTBN_ERR_BITS_ILLEGAL_INSN_BIT);
ASSERT_ERR_BIT_MATCH(kOtbnErrBitsLoop, OTBN_ERR_BITS_LOOP_BIT);
ASSERT_ERR_BIT_MATCH(kOtbnErrBitsImemIntgViolation,
                     OTBN_ERR_BITS_IMEM_INTG_VIOLATION_BIT);
ASSERT_ERR_BIT_MATCH(kOtbnErrBitsDmemIntgViolation,
                     OTBN_ERR_BITS_DMEM_INTG_VIOLATION_BIT);
ASSERT_ERR_BIT_MATCH(kOtbnErrBitsRegIntgViolation,
                     OTBN_ERR_BITS_REG_INTG_VIOLATION_BIT);
ASSERT_ERR_BIT_MATCH(kOtbnErrBitsBusIntgViolation,
                     OTBN_ERR_BITS_BUS_INTG_VIOLATION_BIT);
ASSERT_ERR_BIT_MATCH(kOtbnErrBitsIllegalBusAccess,
                     OTBN_ERR_BITS_ILLEGAL_BUS_ACCESS_BIT);
ASSERT_ERR_BIT_MATCH(kOtbnErrBitsLifecycleEscalation,
                     OTBN_ERR_BITS_LIFECYCLE_ESCALATION_BIT);
ASSERT_ERR_BIT_MATCH(kOtbnErrBitsFatalSoftware,
                     OTBN_ERR_BITS_FATAL_SOFTWARE_BIT);

enum {
  /**
   * Base address for OTBN.
   */
  kBase = TOP_EARLGREY_OTBN_BASE_ADDR,
  /**
   * DMEM size in bytes.
   */
  kOtbnDMemSizeBytes = OTBN_DMEM_SIZE_BYTES,
  /**
   * IMEM size in bytes.
   */
  kOtbnIMemSizeBytes = OTBN_IMEM_SIZE_BYTES,
};

/**
 * OTBN commands
 */
typedef enum otbn_cmd {
  kOtbnCmdExecute = 0xd8,
  kOtbnCmdSecWipeDmem = 0xc3,
  kOtbnCmdSecWipeImem = 0x1e,
} otbn_cmd_t;

/**
 * OTBN status
 */
typedef enum otbn_status {
  kOtbnStatusIdle = 0x00,
  kOtbnStatusBusyExecute = 0x01,
  kOtbnStatusBusySecWipeDmem = 0x02,
  kOtbnStatusBusySecWipeImem = 0x03,
  kOtbnStatusBusySecWipeInt = 0x04,
  kOtbnStatusLocked = 0xFF,
} otbn_status_t;

/**
 * Ensures that `offset_bytes` and `len` are valid for a given `mem_size`.
 */
static otbn_error_t check_offset_len(uint32_t offset_bytes, size_t num_words,
                                     size_t mem_size) {
  if (offset_bytes + num_words * sizeof(uint32_t) <
          num_words * sizeof(uint32_t) ||
      offset_bytes + num_words * sizeof(uint32_t) > mem_size) {
    return kOtbnErrorBadOffsetLen;
  }
  return kOtbnErrorOk;
}

/**
 * Ensures OTBN is idle.
 *
 * If OTBN is busy or locked, this function will return
 * `kOtbnErrorUnavailable`; otherwise it will return `kOtbnErrorOk`.
 *
 * @return Result of the operation.
 */
static otbn_error_t otbn_assert_idle(void) {
  uint32_t status = launder32(~kOtbnStatusIdle);
  otbn_error_t res = launder32(kOtbnErrorOk ^ status);
  status = abs_mmio_read32(kBase + OTBN_STATUS_REG_OFFSET);
  res ^= ~status;
  if (launder32(res) == kOtbnErrorOk) {
    HARDENED_CHECK_EQ(res, kOtbnErrorOk);
    HARDENED_CHECK_EQ(abs_mmio_read32(kBase + OTBN_STATUS_REG_OFFSET),
                      kOtbnStatusIdle);
    return res;
  }
  return kOtbnErrorUnavailable;
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
  // TODO: replace 0 with a random index like the silicon_creator driver
  // (requires an interface to Ibex's RND valid bit and data register).
  size_t i = ((uint64_t)0 * (uint64_t)num_words) >> 32;
  enum { kStep = 1 };
  size_t iter_cnt = 0;
  for (; launder32(iter_cnt) < num_words; ++iter_cnt) {
    abs_mmio_write32(dest_addr + i * sizeof(uint32_t), src[i]);
    i += kStep;
    if (launder32(i) >= num_words) {
      i -= num_words;
    }
    HARDENED_CHECK_LT(i, num_words);
  }
  HARDENED_CHECK_EQ(iter_cnt, num_words);
}

static otbn_error_t otbn_imem_write(size_t num_words, const uint32_t *src,
                                    otbn_addr_t dest) {
  OTBN_RETURN_IF_ERROR(check_offset_len(dest, num_words, kOtbnIMemSizeBytes));
  otbn_write(kBase + OTBN_IMEM_REG_OFFSET + dest, src, num_words);
  return kOtbnErrorOk;
}

otbn_error_t otbn_dmem_write(size_t num_words, const uint32_t *src,
                             otbn_addr_t dest) {
  OTBN_RETURN_IF_ERROR(check_offset_len(dest, num_words, kOtbnDMemSizeBytes));
  otbn_write(kBase + OTBN_DMEM_REG_OFFSET + dest, src, num_words);
  return kOtbnErrorOk;
}

otbn_error_t otbn_dmem_read(size_t num_words, otbn_addr_t src, uint32_t *dest) {
  OTBN_RETURN_IF_ERROR(check_offset_len(src, num_words, kOtbnDMemSizeBytes));

  size_t i = 0;
  for (; launder32(i) < num_words; ++i) {
    dest[i] = abs_mmio_read32(kBase + OTBN_DMEM_REG_OFFSET + src +
                              i * sizeof(uint32_t));
  }
  HARDENED_CHECK_EQ(i, num_words);

  return kOtbnErrorOk;
}

otbn_error_t otbn_execute(void) {
  // Ensure OTBN is idle before attempting to run a command.
  OTBN_RETURN_IF_ERROR(otbn_assert_idle());

  abs_mmio_write32(kBase + OTBN_CMD_REG_OFFSET, kOtbnCmdExecute);
  return kOtbnErrorOk;
}

otbn_error_t otbn_busy_wait_for_done(void) {
  uint32_t status = launder32(UINT32_MAX);
  otbn_error_t res = launder32(kOtbnErrorOk ^ status);
  do {
    status = abs_mmio_read32(kBase + OTBN_STATUS_REG_OFFSET);
  } while (launder32(status) != kOtbnStatusIdle &&
           launder32(status) != kOtbnStatusLocked);
  res ^= ~status;

  otbn_err_bits_t err_bits;
  otbn_err_bits_get(&err_bits);

  if (launder32(res) == kOtbnErrorOk &&
      launder32(err_bits) == kOtbnErrBitsNoError) {
    HARDENED_CHECK_EQ(res, kOtbnErrorOk);
    otbn_err_bits_get(&err_bits);
    HARDENED_CHECK_EQ(err_bits, kOtbnErrBitsNoError);
    HARDENED_CHECK_EQ(abs_mmio_read32(kBase + OTBN_STATUS_REG_OFFSET),
                      kOtbnStatusIdle);
    return res;
  }
  return kOtbnErrorExecutionFailed;
}

void otbn_err_bits_get(otbn_err_bits_t *err_bits) {
  *err_bits = abs_mmio_read32(kBase + OTBN_ERR_BITS_REG_OFFSET);
}

uint32_t otbn_instruction_count_get(void) {
  return abs_mmio_read32(kBase + OTBN_INSN_CNT_REG_OFFSET);
}

otbn_error_t otbn_imem_sec_wipe(void) {
  OTBN_RETURN_IF_ERROR(otbn_assert_idle());
  abs_mmio_write32(kBase + OTBN_CMD_REG_OFFSET, kOtbnCmdSecWipeImem);
  OTBN_RETURN_IF_ERROR(otbn_busy_wait_for_done());
  return kOtbnErrorOk;
}

otbn_error_t otbn_dmem_sec_wipe(void) {
  OTBN_RETURN_IF_ERROR(otbn_assert_idle());
  abs_mmio_write32(kBase + OTBN_CMD_REG_OFFSET, kOtbnCmdSecWipeDmem);
  OTBN_RETURN_IF_ERROR(otbn_busy_wait_for_done());
  return kOtbnErrorOk;
}

otbn_error_t otbn_set_ctrl_software_errs_fatal(bool enable) {
  // Ensure OTBN is idle (otherwise CTRL writes will be ignored).
  OTBN_RETURN_IF_ERROR(otbn_assert_idle());

  // Only one bit in the CTRL register so no need to read current value.
  uint32_t new_ctrl;

  if (enable) {
    new_ctrl = 1;
  } else {
    new_ctrl = 0;
  }

  abs_mmio_write32(kBase + OTBN_CTRL_REG_OFFSET, new_ctrl);

  return kOtbnErrorOk;
}

/**
 * Checks if the OTBN application's IMEM and DMEM address parameters are valid.
 *
 * This function checks the following properties:
 * - IMEM and DMEM ranges must not be "backwards" in memory, with the end
 * address coming before the start address.
 * - The IMEM range must be non-empty.
 *
 * @param app the OTBN application to check
 * @return `kHardenedBoolTrue` if checks pass, otherwise `kHardenedBoolFalse`.
 */
static hardened_bool_t check_app_address_ranges(const otbn_app_t *app) {
  // IMEM must not be backwards or empty.
  if (app->imem_end <= app->imem_start) {
    return kHardenedBoolFalse;
  }
  HARDENED_CHECK_LT(app->imem_start, app->imem_end);

  // DMEM data section must not be backwards.
  if (app->dmem_data_end < app->dmem_data_start) {
    return kHardenedBoolFalse;
  }
  HARDENED_CHECK_LE(app->dmem_data_start, app->dmem_data_end);

  return kHardenedBoolTrue;
}

otbn_error_t otbn_load_app(const otbn_app_t app) {
  if (!check_app_address_ranges(&app)) {
    return kOtbnErrorInvalidArgument;
  }

  // Ensure OTBN is idle.
  OTBN_RETURN_IF_ERROR(otbn_assert_idle());

  const size_t imem_num_words = app.imem_end - app.imem_start;
  const size_t data_num_words = app.dmem_data_end - app.dmem_data_start;

  OTBN_RETURN_IF_ERROR(otbn_imem_sec_wipe());
  OTBN_RETURN_IF_ERROR(otbn_dmem_sec_wipe());

  // IMEM always starts at zero.
  otbn_addr_t imem_start_addr = 0;
  OTBN_RETURN_IF_ERROR(
      otbn_imem_write(imem_num_words, app.imem_start, imem_start_addr));

  if (data_num_words > 0) {
    OTBN_RETURN_IF_ERROR(otbn_dmem_write(data_num_words, app.dmem_data_start,
                                         app.dmem_data_start_addr));
  }

  return kOtbnErrorOk;
}
