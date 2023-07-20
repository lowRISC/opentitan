// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_otbn.h"

#include <assert.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"

#include "otbn_regs.h"  // Generated.

static_assert(kDifOtbnErrBitsBadDataAddr ==
                  (1 << OTBN_ERR_BITS_BAD_DATA_ADDR_BIT),
              "Layout of error bits changed.");
static_assert(kDifOtbnErrBitsBadInsnAddr ==
                  (1 << OTBN_ERR_BITS_BAD_INSN_ADDR_BIT),
              "Layout of error bits changed.");
static_assert(kDifOtbnErrBitsCallStack == (1 << OTBN_ERR_BITS_CALL_STACK_BIT),
              "Layout of error bits changed.");
static_assert(kDifOtbnErrBitsIllegalInsn ==
                  (1 << OTBN_ERR_BITS_ILLEGAL_INSN_BIT),
              "Layout of error bits changed.");
static_assert(kDifOtbnErrBitsLoop == (1 << OTBN_ERR_BITS_LOOP_BIT),
              "Layout of error bits changed.");
static_assert(kDifOtbnErrBitsImemIntgViolation ==
                  (1 << OTBN_ERR_BITS_IMEM_INTG_VIOLATION_BIT),
              "Layout of error bits changed.");
static_assert(kDifOtbnErrBitsDmemIntgViolation ==
                  (1 << OTBN_ERR_BITS_DMEM_INTG_VIOLATION_BIT),
              "Layout of error bits changed.");
static_assert(kDifOtbnErrBitsRegIntgViolation ==
                  (1 << OTBN_ERR_BITS_REG_INTG_VIOLATION_BIT),
              "Layout of error bits changed.");
static_assert(kDifOtbnErrBitsBusIntgViolation ==
                  (1 << OTBN_ERR_BITS_BUS_INTG_VIOLATION_BIT),
              "Layout of error bits changed.");
static_assert(kDifOtbnErrBitsIllegalBusAccess ==
                  (1 << OTBN_ERR_BITS_ILLEGAL_BUS_ACCESS_BIT),
              "Layout of error bits changed.");
static_assert(kDifOtbnErrBitsLifecycleEscalation ==
                  (1 << OTBN_ERR_BITS_LIFECYCLE_ESCALATION_BIT),
              "Layout of error bits changed.");
static_assert(kDifOtbnErrBitsFatalSoftware ==
                  (1 << OTBN_ERR_BITS_FATAL_SOFTWARE_BIT),
              "Layout of error bits changed.");

/**
 * Data width of big number subset, in bytes.
 */
const int kDifOtbnWlenBytes = 256 / 8;

/**
 * Ensures that `offset` and `size` are valid for a given `mem_size`.
 *
 * Valid are 32b word accesses to 32b-aligned memory locations within
 * `mem_size`.
 */
static bool check_offset_len(uint32_t offset_bytes, size_t len_bytes,
                             size_t mem_size) {
  // The overflow check below assumes/requires two unsigned inputs.
  return (len_bytes % sizeof(uint32_t) == 0 &&
          offset_bytes % sizeof(uint32_t) == 0 &&
          offset_bytes + len_bytes >= len_bytes &&
          offset_bytes + len_bytes <= mem_size);
}

dif_result_t dif_otbn_reset(const dif_otbn_t *otbn) {
  if (otbn == NULL) {
    return kDifBadArg;
  }

  mmio_region_write32(otbn->base_addr, OTBN_INTR_ENABLE_REG_OFFSET, 0);

  // Clear all pending interrupts.
  mmio_region_write32(otbn->base_addr, OTBN_INTR_STATE_REG_OFFSET, 0xFFFFFFFF);

  return kDifOk;
}

dif_result_t dif_otbn_write_cmd(const dif_otbn_t *otbn, dif_otbn_cmd_t cmd) {
  if (otbn == NULL) {
    return kDifBadArg;
  }

  mmio_region_write32(otbn->base_addr, OTBN_CMD_REG_OFFSET, cmd);

  return kDifOk;
}

dif_result_t dif_otbn_get_status(const dif_otbn_t *otbn,
                                 dif_otbn_status_t *status) {
  if (otbn == NULL || status == NULL) {
    return kDifBadArg;
  }

  *status = mmio_region_read32(otbn->base_addr, OTBN_STATUS_REG_OFFSET);

  return kDifOk;
}

dif_result_t dif_otbn_get_err_bits(const dif_otbn_t *otbn,
                                   dif_otbn_err_bits_t *err_bits) {
  if (otbn == NULL || err_bits == NULL) {
    return kDifBadArg;
  }

  uint32_t err_bits_raw =
      mmio_region_read32(otbn->base_addr, OTBN_ERR_BITS_REG_OFFSET);

  *err_bits = err_bits_raw;
  return kDifOk;
}

dif_result_t dif_otbn_get_insn_cnt(const dif_otbn_t *otbn, uint32_t *insn_cnt) {
  if (otbn == NULL || insn_cnt == NULL) {
    return kDifBadArg;
  }

  *insn_cnt = mmio_region_read32(otbn->base_addr, OTBN_INSN_CNT_REG_OFFSET);
  return kDifOk;
}

dif_result_t dif_otbn_imem_write(const dif_otbn_t *otbn, uint32_t offset_bytes,
                                 const void *src, size_t len_bytes) {
  if (otbn == NULL || src == NULL ||
      !check_offset_len(offset_bytes, len_bytes, OTBN_IMEM_SIZE_BYTES)) {
    return kDifBadArg;
  }

  mmio_region_memcpy_to_mmio32(
      otbn->base_addr, OTBN_IMEM_REG_OFFSET + offset_bytes, src, len_bytes);

  return kDifOk;
}

dif_result_t dif_otbn_imem_read(const dif_otbn_t *otbn, uint32_t offset_bytes,
                                void *dest, size_t len_bytes) {
  if (otbn == NULL || dest == NULL ||
      !check_offset_len(offset_bytes, len_bytes, OTBN_IMEM_SIZE_BYTES)) {
    return kDifBadArg;
  }

  mmio_region_memcpy_from_mmio32(
      otbn->base_addr, OTBN_IMEM_REG_OFFSET + offset_bytes, dest, len_bytes);

  return kDifOk;
}

dif_result_t dif_otbn_dmem_write(const dif_otbn_t *otbn, uint32_t offset_bytes,
                                 const void *src, size_t len_bytes) {
  if (otbn == NULL || src == NULL ||
      !check_offset_len(offset_bytes, len_bytes, OTBN_DMEM_SIZE_BYTES)) {
    return kDifBadArg;
  }

  mmio_region_memcpy_to_mmio32(
      otbn->base_addr, OTBN_DMEM_REG_OFFSET + offset_bytes, src, len_bytes);

  return kDifOk;
}

dif_result_t dif_otbn_dmem_read(const dif_otbn_t *otbn, uint32_t offset_bytes,
                                void *dest, size_t len_bytes) {
  if (otbn == NULL || dest == NULL ||
      !check_offset_len(offset_bytes, len_bytes, OTBN_DMEM_SIZE_BYTES)) {
    return kDifBadArg;
  }

  mmio_region_memcpy_from_mmio32(
      otbn->base_addr, OTBN_DMEM_REG_OFFSET + offset_bytes, dest, len_bytes);

  return kDifOk;
}

dif_result_t dif_otbn_set_ctrl_software_errs_fatal(const dif_otbn_t *otbn,
                                                   bool enable) {
  if (otbn == NULL) {
    return kDifBadArg;
  }

  // Only one bit in the CTRL register so no need to read current value.
  uint32_t new_ctrl;

  if (enable) {
    new_ctrl = 1;
  } else {
    new_ctrl = 0;
  }

  mmio_region_write32(otbn->base_addr, OTBN_CTRL_REG_OFFSET, new_ctrl);
  if (mmio_region_read32(otbn->base_addr, OTBN_CTRL_REG_OFFSET) != new_ctrl) {
    return kDifUnavailable;
  }

  return kDifOk;
}

size_t dif_otbn_get_dmem_size_bytes(const dif_otbn_t *otbn) {
  return OTBN_DMEM_SIZE_BYTES;
}

size_t dif_otbn_get_imem_size_bytes(const dif_otbn_t *otbn) {
  return OTBN_IMEM_SIZE_BYTES;
}
