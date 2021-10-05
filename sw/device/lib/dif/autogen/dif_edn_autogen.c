// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This file is auto-generated.

#include "sw/device/lib/dif/dif_edn.h"

#include "edn_regs.h"  // Generated.

/**
 * Get the corresponding interrupt register bit offset. INTR_STATE,
 * INTR_ENABLE and INTR_TEST registers have the same bit offsets, so this
 * routine can be reused.
 */
static bool edn_get_irq_bit_index(dif_edn_irq_t irq,
                                  bitfield_bit32_index_t *index_out) {
  switch (irq) {
    case kDifEdnIrqEdnCmdReqDone:
      *index_out = EDN_INTR_STATE_EDN_CMD_REQ_DONE_BIT;
      break;
    case kDifEdnIrqEdnFatalErr:
      *index_out = EDN_INTR_STATE_EDN_FATAL_ERR_BIT;
      break;
    default:
      return false;
  }

  return true;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_irq_get_state(const dif_edn_t *edn,
                                   dif_edn_irq_state_snapshot_t *snapshot) {
  if (edn == NULL || snapshot == NULL) {
    return kDifBadArg;
  }

  *snapshot = mmio_region_read32(edn->base_addr, EDN_INTR_STATE_REG_OFFSET);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_irq_is_pending(const dif_edn_t *edn, dif_edn_irq_t irq,
                                    bool *is_pending) {
  if (edn == NULL || is_pending == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t index;
  if (!edn_get_irq_bit_index(irq, &index)) {
    return kDifBadArg;
  }

  uint32_t intr_state_reg =
      mmio_region_read32(edn->base_addr, EDN_INTR_STATE_REG_OFFSET);

  *is_pending = bitfield_bit32_read(intr_state_reg, index);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_irq_acknowledge(const dif_edn_t *edn, dif_edn_irq_t irq) {
  if (edn == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t index;
  if (!edn_get_irq_bit_index(irq, &index)) {
    return kDifBadArg;
  }

  // Writing to the register clears the corresponding bits (Write-one clear).
  uint32_t intr_state_reg = bitfield_bit32_write(0, index, true);
  mmio_region_write32(edn->base_addr, EDN_INTR_STATE_REG_OFFSET,
                      intr_state_reg);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_irq_force(const dif_edn_t *edn, dif_edn_irq_t irq) {
  if (edn == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t index;
  if (!edn_get_irq_bit_index(irq, &index)) {
    return kDifBadArg;
  }

  uint32_t intr_test_reg = bitfield_bit32_write(0, index, true);
  mmio_region_write32(edn->base_addr, EDN_INTR_TEST_REG_OFFSET, intr_test_reg);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_irq_get_enabled(const dif_edn_t *edn, dif_edn_irq_t irq,
                                     dif_toggle_t *state) {
  if (edn == NULL || state == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t index;
  if (!edn_get_irq_bit_index(irq, &index)) {
    return kDifBadArg;
  }

  uint32_t intr_enable_reg =
      mmio_region_read32(edn->base_addr, EDN_INTR_ENABLE_REG_OFFSET);

  bool is_enabled = bitfield_bit32_read(intr_enable_reg, index);
  *state = is_enabled ? kDifToggleEnabled : kDifToggleDisabled;

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_irq_set_enabled(const dif_edn_t *edn, dif_edn_irq_t irq,
                                     dif_toggle_t state) {
  if (edn == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t index;
  if (!edn_get_irq_bit_index(irq, &index)) {
    return kDifBadArg;
  }

  uint32_t intr_enable_reg =
      mmio_region_read32(edn->base_addr, EDN_INTR_ENABLE_REG_OFFSET);

  bool enable_bit = (state == kDifToggleEnabled) ? true : false;
  intr_enable_reg = bitfield_bit32_write(intr_enable_reg, index, enable_bit);
  mmio_region_write32(edn->base_addr, EDN_INTR_ENABLE_REG_OFFSET,
                      intr_enable_reg);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_irq_disable_all(const dif_edn_t *edn,
                                     dif_edn_irq_enable_snapshot_t *snapshot) {
  if (edn == NULL) {
    return kDifBadArg;
  }

  // Pass the current interrupt state to the caller, if requested.
  if (snapshot != NULL) {
    *snapshot = mmio_region_read32(edn->base_addr, EDN_INTR_ENABLE_REG_OFFSET);
  }

  // Disable all interrupts.
  mmio_region_write32(edn->base_addr, EDN_INTR_ENABLE_REG_OFFSET, 0u);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_irq_restore_all(
    const dif_edn_t *edn, const dif_edn_irq_enable_snapshot_t *snapshot) {
  if (edn == NULL || snapshot == NULL) {
    return kDifBadArg;
  }

  mmio_region_write32(edn->base_addr, EDN_INTR_ENABLE_REG_OFFSET, *snapshot);

  return kDifOk;
}
