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

const size_t kOtbnDMemSizeBytes = OTBN_DMEM_SIZE_BYTES;
const size_t kOtbnIMemSizeBytes = OTBN_IMEM_SIZE_BYTES;

enum { kBase = TOP_EARLGREY_OTBN_BASE_ADDR };

/**
 * Ensures that `offset_bytes` and `len` are valid for a given `mem_size`.
 */
static rom_error_t check_offset_len(uint32_t offset_bytes, size_t num_words,
                                    size_t mem_size) {
  if (offset_bytes + num_words * sizeof(uint32_t) <
          num_words * sizeof(uint32_t) ||
      offset_bytes + num_words * sizeof(uint32_t) > mem_size) {
    return kErrorOtbnBadOffsetLen;
  }
  return kErrorOk;
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

/**
 * Helper function for running an OTBN command.
 *
 * This function blocks until OTBN is idle.
 *
 * @param cmd OTBN command.
 * @param exp_status Expected OTBN status after issuing the command.
 * @param error Error to return if operation fails.
 * @return Result of the operation.
 */
static rom_error_t otbn_cmd_run(otbn_cmd_t cmd, rom_error_t error) {
  enum {
    kIntrStateDone = (1 << OTBN_INTR_COMMON_DONE_BIT),
    // Use a bit index that doesn't overlap with `otbn_err_bits_t`.
    kResDoneBit = 31,
  };
  static_assert((UINT32_C(1) << kResDoneBit) > kOtbnErrBitsLast,
                "kResDoneBit must not overlap with `otbn_err_bits_t`");

  abs_mmio_write32(kBase + OTBN_INTR_STATE_REG_OFFSET, kIntrStateDone);
  abs_mmio_write32(kBase + OTBN_CMD_REG_OFFSET, cmd);

  rom_error_t res = kErrorOk ^ (UINT32_C(1) << kResDoneBit);
  uint32_t reg = 0;
  while (launder32(reg) != kIntrStateDone) {
    reg = abs_mmio_read32(kBase + OTBN_INTR_STATE_REG_OFFSET);
    res ^= bitfield_bit32_read(reg, OTBN_INTR_COMMON_DONE_BIT) << kResDoneBit;
  }
  HARDENED_CHECK_EQ(reg, kIntrStateDone);
  abs_mmio_write32(kBase + OTBN_INTR_STATE_REG_OFFSET, kIntrStateDone);

  otbn_err_bits_t err_bits;
  otbn_err_bits_get(&err_bits);
  res ^= err_bits;

  if (launder32(res) == kErrorOk) {
    HARDENED_CHECK_EQ(res, kErrorOk);
    return res;
  }
  return error;
}

rom_error_t otbn_execute(void) {
  otbn_set_ctrl_software_errs_fatal(true);
  return otbn_cmd_run(kOtbnCmdExecute, kErrorOtbnExecutionFailed);
}

bool otbn_is_busy(void) {
  uint32_t status = abs_mmio_read32(kBase + OTBN_STATUS_REG_OFFSET);
  return status != kOtbnStatusIdle && status != kOtbnStatusLocked;
}

void otbn_err_bits_get(otbn_err_bits_t *err_bits) {
  *err_bits = abs_mmio_read32(kBase + OTBN_ERR_BITS_REG_OFFSET);
}

uint32_t otbn_instruction_count_get(void) {
  return abs_mmio_read32(kBase + OTBN_INSN_CNT_REG_OFFSET);
}

rom_error_t otbn_imem_sec_wipe(void) {
  return otbn_cmd_run(kOtbnCmdSecWipeImem, kErrorOtbnSecWipeImemFailed);
}

rom_error_t otbn_imem_write(uint32_t offset_bytes, const uint32_t *src,
                            size_t num_words) {
  HARDENED_RETURN_IF_ERROR(
      check_offset_len(offset_bytes, num_words, kOtbnIMemSizeBytes));
  otbn_write(kBase + OTBN_IMEM_REG_OFFSET + offset_bytes, src, num_words);
  return kErrorOk;
}

rom_error_t otbn_dmem_sec_wipe(void) {
  return otbn_cmd_run(kOtbnCmdSecWipeDmem, kErrorOtbnSecWipeDmemFailed);
}

rom_error_t otbn_dmem_write(uint32_t offset_bytes, const uint32_t *src,
                            size_t num_words) {
  HARDENED_RETURN_IF_ERROR(
      check_offset_len(offset_bytes, num_words, kOtbnDMemSizeBytes));
  otbn_write(kBase + OTBN_DMEM_REG_OFFSET + offset_bytes, src, num_words);
  return kErrorOk;
}

rom_error_t otbn_dmem_read(uint32_t offset_bytes, uint32_t *dest,
                           size_t num_words) {
  HARDENED_RETURN_IF_ERROR(
      check_offset_len(offset_bytes, num_words, kOtbnDMemSizeBytes));

  size_t i = 0;
  for (; launder32(i) < num_words; ++i) {
    dest[i] = abs_mmio_read32(kBase + OTBN_DMEM_REG_OFFSET + offset_bytes +
                              i * sizeof(uint32_t));
  }
  HARDENED_CHECK_EQ(i, num_words);

  return kErrorOk;
}

void otbn_zero_dmem(void) {
  size_t i = 0;
  for (; launder32(i) < kOtbnDMemSizeBytes; i += sizeof(uint32_t)) {
    abs_mmio_write32(kBase + OTBN_DMEM_REG_OFFSET + i, 0u);
  }
  HARDENED_CHECK_EQ(i, kOtbnDMemSizeBytes);
}

void otbn_set_ctrl_software_errs_fatal(bool enable) {
  // Only one bit in the CTRL register so no need to read current value.
  uint32_t new_ctrl;

  if (enable) {
    new_ctrl = 1;
  } else {
    new_ctrl = 0;
  }

  sec_mmio_write32(kBase + OTBN_CTRL_REG_OFFSET, new_ctrl);
}
