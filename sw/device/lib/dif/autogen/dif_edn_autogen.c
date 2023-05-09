// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/device/lib/dif/autogen/dif_edn_autogen.h"

#include <stdint.h>

#include "sw/device/lib/dif/dif_base.h"

#include "edn_regs.h"  // Generated.

OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_init(mmio_region_t base_addr, dif_edn_t *edn) {
  if (edn == NULL) {
    return kDifBadArg;
  }

  edn->base_addr = base_addr;

  return kDifOk;
}

dif_result_t dif_edn_alert_force(const dif_edn_t *edn, dif_edn_alert_t alert) {
  if (edn == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t alert_idx;
  switch (alert) {
    case kDifEdnAlertRecovAlert:
      alert_idx = EDN_ALERT_TEST_RECOV_ALERT_BIT;
      break;
    case kDifEdnAlertFatalAlert:
      alert_idx = EDN_ALERT_TEST_FATAL_ALERT_BIT;
      break;
    default:
      return kDifBadArg;
  }

  uint32_t alert_test_reg = bitfield_bit32_write(0, alert_idx, true);
  mmio_region_write32(edn->base_addr, (ptrdiff_t)EDN_ALERT_TEST_REG_OFFSET,
                      alert_test_reg);

  return kDifOk;
}

/**
 * Get the corresponding interrupt register bit offset of the IRQ.
 */
static bool edn_get_irq_bit_index(dif_edn_irq_t irq,
                                  bitfield_bit32_index_t *index_out) {
  switch (irq) {
    case kDifEdnIrqEdnCmdReqDone:
      *index_out = EDN_INTR_COMMON_EDN_CMD_REQ_DONE_BIT;
      break;
    case kDifEdnIrqEdnFatalErr:
      *index_out = EDN_INTR_COMMON_EDN_FATAL_ERR_BIT;
      break;
    default:
      return false;
  }

  return true;
}

static dif_irq_type_t irq_types[] = {
    kDifIrqTypeEvent,
    kDifIrqTypeEvent,
};

OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_irq_get_type(const dif_edn_t *edn, dif_edn_irq_t irq,
                                  dif_irq_type_t *type) {
  if (edn == NULL || type == NULL || irq == kDifEdnIrqEdnFatalErr + 1) {
    return kDifBadArg;
  }

  *type = irq_types[irq];

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_irq_get_state(const dif_edn_t *edn,
                                   dif_edn_irq_state_snapshot_t *snapshot) {
  if (edn == NULL || snapshot == NULL) {
    return kDifBadArg;
  }

  *snapshot =
      mmio_region_read32(edn->base_addr, (ptrdiff_t)EDN_INTR_STATE_REG_OFFSET);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_irq_acknowledge_state(
    const dif_edn_t *edn, dif_edn_irq_state_snapshot_t snapshot) {
  if (edn == NULL) {
    return kDifBadArg;
  }

  mmio_region_write32(edn->base_addr, (ptrdiff_t)EDN_INTR_STATE_REG_OFFSET,
                      snapshot);

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
      mmio_region_read32(edn->base_addr, (ptrdiff_t)EDN_INTR_STATE_REG_OFFSET);

  *is_pending = bitfield_bit32_read(intr_state_reg, index);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_irq_acknowledge_all(const dif_edn_t *edn) {
  if (edn == NULL) {
    return kDifBadArg;
  }

  // Writing to the register clears the corresponding bits (Write-one clear).
  mmio_region_write32(edn->base_addr, (ptrdiff_t)EDN_INTR_STATE_REG_OFFSET,
                      UINT32_MAX);

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
  mmio_region_write32(edn->base_addr, (ptrdiff_t)EDN_INTR_STATE_REG_OFFSET,
                      intr_state_reg);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_irq_force(const dif_edn_t *edn, dif_edn_irq_t irq,
                               const bool val) {
  if (edn == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t index;
  if (!edn_get_irq_bit_index(irq, &index)) {
    return kDifBadArg;
  }

  uint32_t intr_test_reg = bitfield_bit32_write(0, index, val);
  mmio_region_write32(edn->base_addr, (ptrdiff_t)EDN_INTR_TEST_REG_OFFSET,
                      intr_test_reg);

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
      mmio_region_read32(edn->base_addr, (ptrdiff_t)EDN_INTR_ENABLE_REG_OFFSET);

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
      mmio_region_read32(edn->base_addr, (ptrdiff_t)EDN_INTR_ENABLE_REG_OFFSET);

  bool enable_bit = (state == kDifToggleEnabled) ? true : false;
  intr_enable_reg = bitfield_bit32_write(intr_enable_reg, index, enable_bit);
  mmio_region_write32(edn->base_addr, (ptrdiff_t)EDN_INTR_ENABLE_REG_OFFSET,
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
    *snapshot = mmio_region_read32(edn->base_addr,
                                   (ptrdiff_t)EDN_INTR_ENABLE_REG_OFFSET);
  }

  // Disable all interrupts.
  mmio_region_write32(edn->base_addr, (ptrdiff_t)EDN_INTR_ENABLE_REG_OFFSET,
                      0u);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_irq_restore_all(
    const dif_edn_t *edn, const dif_edn_irq_enable_snapshot_t *snapshot) {
  if (edn == NULL || snapshot == NULL) {
    return kDifBadArg;
  }

  mmio_region_write32(edn->base_addr, (ptrdiff_t)EDN_INTR_ENABLE_REG_OFFSET,
                      *snapshot);

  return kDifOk;
}
