// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_otbn.h"

#include "sw/device/lib/base/bitfield.h"

#include "otbn_regs.h"  // Generated.

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
      offset = OTBN_INTR_COMMON_DONE;
      break;
    case kDifOtbnInterruptErr:
      offset = OTBN_INTR_COMMON_ERR;
      break;
    default:
      return false;
  }

  *offset_out = offset;

  return true;
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
  if (otbn == NULL || start_addr % 4 != 0 ||
      start_addr >= OTBN_IMEM_SIZE_BYTES) {
    return kDifOtbnBadArg;
  }

  mmio_region_write32(otbn->base_addr, OTBN_START_ADDR_REG_OFFSET, start_addr);

  uint32_t cmd_reg_val = 0x0u;
  cmd_reg_val = bitfield_bit32_write(cmd_reg_val, OTBN_CMD_START, true);
  mmio_region_write32(otbn->base_addr, OTBN_CMD_REG_OFFSET, cmd_reg_val);

  return kDifOtbnOk;
}

dif_otbn_result_t dif_otbn_is_busy(const dif_otbn_t *otbn, bool *busy) {
  if (otbn == NULL || busy == NULL) {
    return kDifOtbnBadArg;
  }

  uint32_t status = mmio_region_read32(otbn->base_addr, OTBN_STATUS_REG_OFFSET);
  *busy =
      bitfield_field32_read(status, (bitfield_field32_t){
                                        .mask = 1, .index = OTBN_STATUS_BUSY,
                                    });

  return kDifOtbnOk;
}

dif_otbn_result_t dif_otbn_get_err_code(const dif_otbn_t *otbn,
                                        dif_otbn_err_code_t *err_code) {
  if (otbn == NULL || err_code == NULL) {
    return kDifOtbnBadArg;
  }

  uint32_t err_code_raw =
      mmio_region_read32(otbn->base_addr, OTBN_ERR_CODE_REG_OFFSET);

  // Ensure that all values returned from hardware match explicitly defined
  // values in the DIF.
  switch (err_code_raw) {
    case kDifOtbnErrCodeNoError:
    case kDifOtbnErrCodeBadDataAddr:
      *err_code = (dif_otbn_err_code_t)err_code_raw;
      return kDifOtbnOk;

    default:
      return kDifOtbnUnexpectedData;
  }
}

dif_otbn_result_t dif_otbn_imem_write(const dif_otbn_t *otbn,
                                      uint32_t offset_bytes,
                                      const uint32_t *src, size_t len_bytes) {
  // Only 32b-aligned 32b word accesses are allowed.
  if (otbn == NULL || src == NULL || len_bytes % 4 != 0 ||
      offset_bytes % 4 != 0 ||
      offset_bytes + len_bytes > OTBN_IMEM_SIZE_BYTES) {
    return kDifOtbnBadArg;
  }

  mmio_region_memcpy_to_mmio32(
      otbn->base_addr, OTBN_IMEM_REG_OFFSET + offset_bytes, src, len_bytes);

  return kDifOtbnOk;
}

dif_otbn_result_t dif_otbn_imem_read(const dif_otbn_t *otbn,
                                     uint32_t offset_bytes, uint32_t *dest,
                                     size_t len_bytes) {
  // Only 32b-aligned 32b word accesses are allowed.
  if (otbn == NULL || dest == NULL || len_bytes % 4 != 0 ||
      offset_bytes % 4 != 0 ||
      offset_bytes + len_bytes > OTBN_IMEM_SIZE_BYTES) {
    return kDifOtbnBadArg;
  }

  mmio_region_memcpy_from_mmio32(
      otbn->base_addr, OTBN_IMEM_REG_OFFSET + offset_bytes, dest, len_bytes);

  return kDifOtbnOk;
}

dif_otbn_result_t dif_otbn_dmem_write(const dif_otbn_t *otbn,
                                      uint32_t offset_bytes,
                                      const uint32_t *src, size_t len_bytes) {
  // Only 32b-aligned 32b word accesses are allowed.
  if (otbn == NULL || src == NULL || len_bytes % 4 != 0 ||
      offset_bytes % 4 != 0 ||
      offset_bytes + len_bytes > OTBN_DMEM_SIZE_BYTES) {
    return kDifOtbnBadArg;
  }

  mmio_region_memcpy_to_mmio32(
      otbn->base_addr, OTBN_DMEM_REG_OFFSET + offset_bytes, src, len_bytes);

  return kDifOtbnOk;
}

dif_otbn_result_t dif_otbn_dmem_read(const dif_otbn_t *otbn,
                                     uint32_t offset_bytes, uint32_t *dest,
                                     size_t len_bytes) {
  // Only 32b-aligned 32b word accesses are allowed.
  if (otbn == NULL || dest == NULL || len_bytes % 4 != 0 ||
      offset_bytes % 4 != 0 ||
      offset_bytes + len_bytes > OTBN_DMEM_SIZE_BYTES) {
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
