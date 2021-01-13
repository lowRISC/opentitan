// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_otbn.h"

#include "sw/device/lib/base/bitfield.h"

#include "otbn_regs.h"  // Generated.

_Static_assert(kDifOtbnErrBitsBadDataAddr ==
                   (1 << OTBN_ERR_BITS_BAD_DATA_ADDR_BIT),
               "Layout of error bits changed.");
_Static_assert(kDifOtbnErrBitsBadInsnAddr ==
                   (1 << OTBN_ERR_BITS_BAD_INSN_ADDR_BIT),
               "Layout of error bits changed.");
_Static_assert(kDifOtbnErrBitsCallStack == (1 << OTBN_ERR_BITS_CALL_STACK_BIT),
               "Layout of error bits changed.");
_Static_assert(kDifOtbnErrBitsIllegalInsn ==
                   (1 << OTBN_ERR_BITS_ILLEGAL_INSN_BIT),
               "Layout of error bits changed.");
_Static_assert(kDifOtbnErrBitsLoop == (1 << OTBN_ERR_BITS_LOOP_BIT),
               "Layout of error bits changed.");
_Static_assert(kDifOtbnErrBitsFatalImem == (1 << OTBN_ERR_BITS_FATAL_IMEM_BIT),
               "Layout of error bits changed.");
_Static_assert(kDifOtbnErrBitsFatalDmem == (1 << OTBN_ERR_BITS_FATAL_DMEM_BIT),
               "Layout of error bits changed.");
_Static_assert(kDifOtbnErrBitsFatalReg == (1 << OTBN_ERR_BITS_FATAL_REG_BIT),
               "Layout of error bits changed.");

/**
 * Data width of big number subset, in bytes.
 */
const int kDifOtbnWlenBytes = 256 / 8;

/**
 * Convert from a `dif_otbn_interrupt_t` to the appropriate bit index.
 *
 * INTR_STATE, INTR_ENABLE, and INTR_TEST registers have the same bit offset.
 */
static bool irq_bit_index_get(dif_otbn_interrupt_t irq_type,
                              uint8_t *offset_out) {
  ptrdiff_t offset;
  switch (irq_type) {
    case kDifOtbnInterruptDone:
      offset = OTBN_INTR_COMMON_DONE_BIT;
      break;
    default:
      return false;
  }

  *offset_out = offset;

  return true;
}

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

dif_otbn_result_t dif_otbn_init(const dif_otbn_config_t *config,
                                dif_otbn_t *otbn) {
  if (config == NULL || otbn == NULL) {
    return kDifOtbnBadArg;
  }

  otbn->base_addr = config->base_addr;
  dif_otbn_reset(otbn);

  return kDifOtbnOk;
}

dif_otbn_result_t dif_otbn_reset(const dif_otbn_t *otbn) {
  if (otbn == NULL) {
    return kDifOtbnBadArg;
  }

  mmio_region_write32(otbn->base_addr, OTBN_INTR_ENABLE_REG_OFFSET, 0);

  // Clear all pending interrupts.
  mmio_region_write32(otbn->base_addr, OTBN_INTR_STATE_REG_OFFSET, 0xFFFFFFFF);

  return kDifOtbnOk;
}

dif_otbn_result_t dif_otbn_irq_state_get(const dif_otbn_t *otbn,
                                         dif_otbn_interrupt_t irq_type,
                                         dif_otbn_enable_t *state) {
  if (otbn == NULL || state == NULL) {
    return kDifOtbnBadArg;
  }

  uint8_t bit_index;
  if (!irq_bit_index_get(irq_type, &bit_index)) {
    return kDifOtbnError;
  }

  bool enabled = bitfield_bit32_read(
      mmio_region_read32(otbn->base_addr, OTBN_INTR_STATE_REG_OFFSET),
      bit_index);
  *state = (enabled ? kDifOtbnEnable : kDifOtbnDisable);

  return kDifOtbnOk;
}

dif_otbn_result_t dif_otbn_irq_state_clear(const dif_otbn_t *otbn,
                                           dif_otbn_interrupt_t irq_type) {
  if (otbn == NULL) {
    return kDifOtbnBadArg;
  }

  uint8_t bit_index;
  if (!irq_bit_index_get(irq_type, &bit_index)) {
    return kDifOtbnError;
  }

  uint32_t register_value = 0x0u;
  register_value = bitfield_bit32_write(register_value, bit_index, true);
  mmio_region_write32(otbn->base_addr, OTBN_INTR_STATE_REG_OFFSET,
                      register_value);

  return kDifOtbnOk;
}

dif_otbn_result_t dif_otbn_irqs_disable(const dif_otbn_t *otbn,
                                        uint32_t *state) {
  if (otbn == NULL) {
    return kDifOtbnBadArg;
  }

  // Pass the interrupt state back to the caller.
  if (state != NULL) {
    *state = mmio_region_read32(otbn->base_addr, OTBN_INTR_ENABLE_REG_OFFSET);
  }

  // Disable all interrupts.
  mmio_region_write32(otbn->base_addr, OTBN_INTR_ENABLE_REG_OFFSET, 0u);

  return kDifOtbnOk;
}

dif_otbn_result_t dif_otbn_irqs_restore(const dif_otbn_t *otbn,
                                        uint32_t state) {
  if (otbn == NULL) {
    return kDifOtbnBadArg;
  }

  // Restore interrupt state.
  mmio_region_write32(otbn->base_addr, OTBN_INTR_ENABLE_REG_OFFSET, state);

  return kDifOtbnOk;
}

dif_otbn_result_t dif_otbn_irq_control(const dif_otbn_t *otbn,
                                       dif_otbn_interrupt_t irq_type,
                                       dif_otbn_enable_t enable) {
  if (otbn == NULL) {
    return kDifOtbnBadArg;
  }

  uint8_t bit_index;
  if (!irq_bit_index_get(irq_type, &bit_index)) {
    return kDifOtbnError;
  }

  // Enable/Disable interrupt.
  uint32_t register_value =
      mmio_region_read32(otbn->base_addr, OTBN_INTR_ENABLE_REG_OFFSET);
  register_value = bitfield_bit32_write(register_value, bit_index,
                                        (enable == kDifOtbnEnable));
  mmio_region_write32(otbn->base_addr, OTBN_INTR_ENABLE_REG_OFFSET,
                      register_value);

  return kDifOtbnOk;
}

dif_otbn_result_t dif_otbn_irq_force(const dif_otbn_t *otbn,
                                     dif_otbn_interrupt_t irq_type) {
  if (otbn == NULL) {
    return kDifOtbnBadArg;
  }

  uint8_t bit_index;
  if (!irq_bit_index_get(irq_type, &bit_index)) {
    return kDifOtbnError;
  }

  // Force the requested interrupt.
  uint32_t register_value =
      mmio_region_read32(otbn->base_addr, OTBN_INTR_TEST_REG_OFFSET);
  register_value = bitfield_bit32_write(register_value, bit_index, true);
  mmio_region_write32(otbn->base_addr, OTBN_INTR_TEST_REG_OFFSET,
                      register_value);

  return kDifOtbnOk;
}

dif_otbn_result_t dif_otbn_start(const dif_otbn_t *otbn,
                                 unsigned int start_addr) {
  if (otbn == NULL || start_addr % sizeof(uint32_t) != 0 ||
      start_addr >= OTBN_IMEM_SIZE_BYTES) {
    return kDifOtbnBadArg;
  }

  mmio_region_write32(otbn->base_addr, OTBN_START_ADDR_REG_OFFSET, start_addr);

  uint32_t cmd_reg_val = 0x0u;
  cmd_reg_val = bitfield_bit32_write(cmd_reg_val, OTBN_CMD_START_BIT, true);
  mmio_region_write32(otbn->base_addr, OTBN_CMD_REG_OFFSET, cmd_reg_val);

  return kDifOtbnOk;
}

dif_otbn_result_t dif_otbn_is_busy(const dif_otbn_t *otbn, bool *busy) {
  if (otbn == NULL || busy == NULL) {
    return kDifOtbnBadArg;
  }

  uint32_t status = mmio_region_read32(otbn->base_addr, OTBN_STATUS_REG_OFFSET);
  *busy = bitfield_bit32_read(status, OTBN_STATUS_BUSY_BIT);

  return kDifOtbnOk;
}

dif_otbn_result_t dif_otbn_get_err_bits(const dif_otbn_t *otbn,
                                        dif_otbn_err_bits_t *err_bits) {
  if (otbn == NULL || err_bits == NULL) {
    return kDifOtbnBadArg;
  }

  uint32_t err_bits_raw =
      mmio_region_read32(otbn->base_addr, OTBN_ERR_BITS_REG_OFFSET);

  *err_bits = err_bits_raw;
  return kDifOtbnOk;
}

dif_otbn_result_t dif_otbn_imem_write(const dif_otbn_t *otbn,
                                      uint32_t offset_bytes, const void *src,
                                      size_t len_bytes) {
  if (otbn == NULL || src == NULL ||
      !check_offset_len(offset_bytes, len_bytes, OTBN_IMEM_SIZE_BYTES)) {
    return kDifOtbnBadArg;
  }

  mmio_region_memcpy_to_mmio32(
      otbn->base_addr, OTBN_IMEM_REG_OFFSET + offset_bytes, src, len_bytes);

  return kDifOtbnOk;
}

dif_otbn_result_t dif_otbn_imem_read(const dif_otbn_t *otbn,
                                     uint32_t offset_bytes, void *dest,
                                     size_t len_bytes) {
  if (otbn == NULL || dest == NULL ||
      !check_offset_len(offset_bytes, len_bytes, OTBN_IMEM_SIZE_BYTES)) {
    return kDifOtbnBadArg;
  }

  mmio_region_memcpy_from_mmio32(
      otbn->base_addr, OTBN_IMEM_REG_OFFSET + offset_bytes, dest, len_bytes);

  return kDifOtbnOk;
}

dif_otbn_result_t dif_otbn_dmem_write(const dif_otbn_t *otbn,
                                      uint32_t offset_bytes, const void *src,
                                      size_t len_bytes) {
  if (otbn == NULL || src == NULL ||
      !check_offset_len(offset_bytes, len_bytes, OTBN_DMEM_SIZE_BYTES)) {
    return kDifOtbnBadArg;
  }

  mmio_region_memcpy_to_mmio32(
      otbn->base_addr, OTBN_DMEM_REG_OFFSET + offset_bytes, src, len_bytes);

  return kDifOtbnOk;
}

dif_otbn_result_t dif_otbn_dmem_read(const dif_otbn_t *otbn,
                                     uint32_t offset_bytes, void *dest,
                                     size_t len_bytes) {
  if (otbn == NULL || dest == NULL ||
      !check_offset_len(offset_bytes, len_bytes, OTBN_IMEM_SIZE_BYTES)) {
    return kDifOtbnBadArg;
  }

  mmio_region_memcpy_from_mmio32(
      otbn->base_addr, OTBN_DMEM_REG_OFFSET + offset_bytes, dest, len_bytes);

  return kDifOtbnOk;
}

size_t dif_otbn_get_dmem_size_bytes(const dif_otbn_t *otbn) {
  return OTBN_DMEM_SIZE_BYTES;
}

size_t dif_otbn_get_imem_size_bytes(const dif_otbn_t *otbn) {
  return OTBN_IMEM_SIZE_BYTES;
}
