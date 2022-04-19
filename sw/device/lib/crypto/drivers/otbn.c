// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/otbn.h"

#include <assert.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"

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

void otbn_execute(void) {
  abs_mmio_write32(TOP_EARLGREY_OTBN_BASE_ADDR + OTBN_CMD_REG_OFFSET,
                   kOtbnCmdExecute);
}

bool otbn_is_busy(void) {
  uint32_t status =
      abs_mmio_read32(TOP_EARLGREY_OTBN_BASE_ADDR + OTBN_STATUS_REG_OFFSET);
  return status != kOtbnStatusIdle && status != kOtbnStatusLocked;
}

void otbn_get_err_bits(otbn_err_bits_t *err_bits) {
  *err_bits =
      abs_mmio_read32(TOP_EARLGREY_OTBN_BASE_ADDR + OTBN_ERR_BITS_REG_OFFSET);
}

otbn_error_t otbn_imem_write(uint32_t offset_bytes, const uint32_t *src,
                             size_t num_words) {
  OTBN_RETURN_IF_ERROR(
      check_offset_len(offset_bytes, num_words, kOtbnIMemSizeBytes));

  for (size_t i = 0; i < num_words; ++i) {
    abs_mmio_write32(TOP_EARLGREY_OTBN_BASE_ADDR + OTBN_IMEM_REG_OFFSET +
                         offset_bytes + i * sizeof(uint32_t),
                     src[i]);
  }

  return kOtbnErrorOk;
}

otbn_error_t otbn_dmem_write(uint32_t offset_bytes, const uint32_t *src,
                             size_t num_words) {
  OTBN_RETURN_IF_ERROR(
      check_offset_len(offset_bytes, num_words, kOtbnDMemSizeBytes));

  for (size_t i = 0; i < num_words; ++i) {
    abs_mmio_write32(TOP_EARLGREY_OTBN_BASE_ADDR + OTBN_DMEM_REG_OFFSET +
                         offset_bytes + i * sizeof(uint32_t),
                     src[i]);
  }

  return kOtbnErrorOk;
}

otbn_error_t otbn_dmem_read(uint32_t offset_bytes, uint32_t *dest,
                            size_t num_words) {
  OTBN_RETURN_IF_ERROR(
      check_offset_len(offset_bytes, num_words, kOtbnDMemSizeBytes));

  for (size_t i = 0; i < num_words; ++i) {
    dest[i] =
        abs_mmio_read32(TOP_EARLGREY_OTBN_BASE_ADDR + OTBN_DMEM_REG_OFFSET +
                        offset_bytes + i * sizeof(uint32_t));
  }

  return kOtbnErrorOk;
}

void otbn_zero_dmem(void) {
  for (size_t i = 0; i < kOtbnDMemSizeBytes; i += sizeof(uint32_t)) {
    abs_mmio_write32(TOP_EARLGREY_OTBN_BASE_ADDR + OTBN_DMEM_REG_OFFSET + i,
                     0u);
  }
}

otbn_error_t otbn_set_ctrl_software_errs_fatal(bool enable) {
  // Only one bit in the CTRL register so no need to read current value.
  uint32_t new_ctrl;

  if (enable) {
    new_ctrl = 1;
  } else {
    new_ctrl = 0;
  }

  abs_mmio_write32(TOP_EARLGREY_OTBN_BASE_ADDR + OTBN_CTRL_REG_OFFSET,
                   new_ctrl);
  if (abs_mmio_read32(TOP_EARLGREY_OTBN_BASE_ADDR + OTBN_CTRL_REG_OFFSET) !=
      new_ctrl) {
    return kOtbnErrorUnavailable;
  }

  return kOtbnErrorOk;
}
