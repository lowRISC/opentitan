// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/otbn.h"

#include <assert.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/silicon_creator/lib/base/abs_mmio.h"
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
ASSERT_ERR_BIT_MATCH(kOtbnErrBitsIllegalBusAccess,
                     OTBN_ERR_BITS_ILLEGAL_BUS_ACCESS_BIT);
ASSERT_ERR_BIT_MATCH(kOtbnErrBitsLifecycleEscalation,
                     OTBN_ERR_BITS_LIFECYCLE_ESCALATION_BIT);

const size_t kOtbnDMemSizeBytes = OTBN_DMEM_SIZE_BYTES;
const size_t kOtbnIMemSizeBytes = OTBN_IMEM_SIZE_BYTES;

enum { kBase = TOP_EARLGREY_OTBN_BASE_ADDR };

/**
 * Ensures that `offset_bytes` and `len` are valid for a given `mem_size`.
 */
static rom_error_t check_offset_len(uint32_t offset_bytes, size_t len,
                                    size_t mem_size) {
  // TODO: Update to use alignment utility functions.
  // https://github.com/lowRISC/opentitan/issues/6112
  if (offset_bytes % sizeof(uint32_t) != 0) {
    return kErrorOtbnBadOffset;
  }
  if (offset_bytes + len * sizeof(uint32_t) < len * sizeof(uint32_t) ||
      offset_bytes + len * sizeof(uint32_t) > mem_size) {
    return kErrorOtbnBadOffsetLen;
  }
  return kErrorOk;
}

rom_error_t otbn_start(uint32_t start_addr) {
  // TODO: Update to use alignment utility functions.
  // https://github.com/lowRISC/opentitan/issues/6112
  if (start_addr % sizeof(uint32_t) != 0 || start_addr >= kOtbnIMemSizeBytes) {
    return kErrorOtbnInvalidArgument;
  }

  abs_mmio_write32(kBase + OTBN_START_ADDR_REG_OFFSET, start_addr);
  abs_mmio_write32(kBase + OTBN_CMD_REG_OFFSET, kOtbnCmdExecute);

  return kErrorOk;
}

bool otbn_is_busy() {
  uint32_t status = abs_mmio_read32(kBase + OTBN_STATUS_REG_OFFSET);
  return status != kOtbnStatusIdle;
}

void otbn_get_err_bits(otbn_err_bits_t *err_bits) {
  *err_bits = abs_mmio_read32(kBase + OTBN_ERR_BITS_REG_OFFSET);
}

rom_error_t otbn_imem_write(uint32_t offset_bytes, const uint32_t *src,
                            size_t len) {
  RETURN_IF_ERROR(check_offset_len(offset_bytes, len, kOtbnIMemSizeBytes));

  for (size_t i = 0; i < len; ++i, offset_bytes += sizeof(uint32_t)) {
    abs_mmio_write32(kBase + OTBN_IMEM_REG_OFFSET + offset_bytes, src[i]);
  }

  return kErrorOk;
}

rom_error_t otbn_dmem_write(uint32_t offset_bytes, const uint32_t *src,
                            size_t len) {
  RETURN_IF_ERROR(check_offset_len(offset_bytes, len, kOtbnDMemSizeBytes));

  for (size_t i = 0; i < len; ++i, offset_bytes += sizeof(uint32_t)) {
    abs_mmio_write32(kBase + OTBN_DMEM_REG_OFFSET + offset_bytes, src[i]);
  }

  return kErrorOk;
}

rom_error_t otbn_dmem_read(uint32_t offset_bytes, uint32_t *dest, size_t len) {
  RETURN_IF_ERROR(check_offset_len(offset_bytes, len, kOtbnDMemSizeBytes));

  for (size_t i = 0; i < len; ++i, offset_bytes += sizeof(uint32_t)) {
    dest[i] = abs_mmio_read32(kBase + OTBN_DMEM_REG_OFFSET + offset_bytes);
  }

  return kErrorOk;
}
