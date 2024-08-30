// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/device/lib/dif/autogen/dif_i2c_autogen.h"

#include <stdint.h>

#include "sw/device/lib/dif/dif_base.h"

#include "i2c_regs.h"  // Generated.

OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_init(mmio_region_t base_addr, dif_i2c_t *i2c) {
  if (i2c == NULL) {
    return kDifBadArg;
  }

  i2c->base_addr = base_addr;

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_init_from_dt(const dt_i2c_t *dt, dif_i2c_t *i2c) {
  if (i2c == NULL || dt == NULL) {
    return kDifBadArg;
  }

  i2c->base_addr =
      mmio_region_from_addr(dt_i2c_reg_block(dt, kDtI2cRegBlockDefault));

  return kDifOk;
}

dif_result_t dif_i2c_alert_force(const dif_i2c_t *i2c, dif_i2c_alert_t alert) {
  if (i2c == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t alert_idx;
  switch (alert) {
    case kDifI2cAlertFatalFault:
      alert_idx = I2C_ALERT_TEST_FATAL_FAULT_BIT;
      break;
    default:
      return kDifBadArg;
  }

  uint32_t alert_test_reg = bitfield_bit32_write(0, alert_idx, true);
  mmio_region_write32(i2c->base_addr, (ptrdiff_t)I2C_ALERT_TEST_REG_OFFSET,
                      alert_test_reg);

  return kDifOk;
}

/**
 * Get the corresponding interrupt register bit offset of the IRQ.
 */
static bool i2c_get_irq_bit_index(dif_i2c_irq_t irq,
                                  bitfield_bit32_index_t *index_out) {
  switch (irq) {
    case kDtI2cIrqFmtThreshold:
      *index_out = I2C_INTR_COMMON_FMT_THRESHOLD_BIT;
      break;
    case kDtI2cIrqRxThreshold:
      *index_out = I2C_INTR_COMMON_RX_THRESHOLD_BIT;
      break;
    case kDtI2cIrqAcqThreshold:
      *index_out = I2C_INTR_COMMON_ACQ_THRESHOLD_BIT;
      break;
    case kDtI2cIrqRxOverflow:
      *index_out = I2C_INTR_COMMON_RX_OVERFLOW_BIT;
      break;
    case kDtI2cIrqControllerHalt:
      *index_out = I2C_INTR_COMMON_CONTROLLER_HALT_BIT;
      break;
    case kDtI2cIrqSclInterference:
      *index_out = I2C_INTR_COMMON_SCL_INTERFERENCE_BIT;
      break;
    case kDtI2cIrqSdaInterference:
      *index_out = I2C_INTR_COMMON_SDA_INTERFERENCE_BIT;
      break;
    case kDtI2cIrqStretchTimeout:
      *index_out = I2C_INTR_COMMON_STRETCH_TIMEOUT_BIT;
      break;
    case kDtI2cIrqSdaUnstable:
      *index_out = I2C_INTR_COMMON_SDA_UNSTABLE_BIT;
      break;
    case kDtI2cIrqCmdComplete:
      *index_out = I2C_INTR_COMMON_CMD_COMPLETE_BIT;
      break;
    case kDtI2cIrqTxStretch:
      *index_out = I2C_INTR_COMMON_TX_STRETCH_BIT;
      break;
    case kDtI2cIrqTxThreshold:
      *index_out = I2C_INTR_COMMON_TX_THRESHOLD_BIT;
      break;
    case kDtI2cIrqAcqStretch:
      *index_out = I2C_INTR_COMMON_ACQ_STRETCH_BIT;
      break;
    case kDtI2cIrqUnexpStop:
      *index_out = I2C_INTR_COMMON_UNEXP_STOP_BIT;
      break;
    case kDtI2cIrqHostTimeout:
      *index_out = I2C_INTR_COMMON_HOST_TIMEOUT_BIT;
      break;
    default:
      return false;
  }

  return true;
}

static dif_irq_type_t irq_types[] = {
    kDifIrqTypeStatus, kDifIrqTypeStatus, kDifIrqTypeStatus, kDifIrqTypeEvent,
    kDifIrqTypeStatus, kDifIrqTypeEvent,  kDifIrqTypeEvent,  kDifIrqTypeEvent,
    kDifIrqTypeEvent,  kDifIrqTypeEvent,  kDifIrqTypeStatus, kDifIrqTypeStatus,
    kDifIrqTypeStatus, kDifIrqTypeEvent,  kDifIrqTypeEvent,
};

OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_irq_get_type(const dif_i2c_t *i2c, dif_i2c_irq_t irq,
                                  dif_irq_type_t *type) {
  if (i2c == NULL || type == NULL || irq == kDtI2cIrqCount) {
    return kDifBadArg;
  }

  *type = irq_types[irq];

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_irq_get_state(const dif_i2c_t *i2c,
                                   dif_i2c_irq_state_snapshot_t *snapshot) {
  if (i2c == NULL || snapshot == NULL) {
    return kDifBadArg;
  }

  *snapshot =
      mmio_region_read32(i2c->base_addr, (ptrdiff_t)I2C_INTR_STATE_REG_OFFSET);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_irq_acknowledge_state(
    const dif_i2c_t *i2c, dif_i2c_irq_state_snapshot_t snapshot) {
  if (i2c == NULL) {
    return kDifBadArg;
  }

  mmio_region_write32(i2c->base_addr, (ptrdiff_t)I2C_INTR_STATE_REG_OFFSET,
                      snapshot);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_irq_is_pending(const dif_i2c_t *i2c, dif_i2c_irq_t irq,
                                    bool *is_pending) {
  if (i2c == NULL || is_pending == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t index;
  if (!i2c_get_irq_bit_index(irq, &index)) {
    return kDifBadArg;
  }

  uint32_t intr_state_reg =
      mmio_region_read32(i2c->base_addr, (ptrdiff_t)I2C_INTR_STATE_REG_OFFSET);

  *is_pending = bitfield_bit32_read(intr_state_reg, index);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_irq_acknowledge_all(const dif_i2c_t *i2c) {
  if (i2c == NULL) {
    return kDifBadArg;
  }

  // Writing to the register clears the corresponding bits (Write-one clear).
  mmio_region_write32(i2c->base_addr, (ptrdiff_t)I2C_INTR_STATE_REG_OFFSET,
                      UINT32_MAX);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_irq_acknowledge(const dif_i2c_t *i2c, dif_i2c_irq_t irq) {
  if (i2c == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t index;
  if (!i2c_get_irq_bit_index(irq, &index)) {
    return kDifBadArg;
  }

  // Writing to the register clears the corresponding bits (Write-one clear).
  uint32_t intr_state_reg = bitfield_bit32_write(0, index, true);
  mmio_region_write32(i2c->base_addr, (ptrdiff_t)I2C_INTR_STATE_REG_OFFSET,
                      intr_state_reg);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_irq_force(const dif_i2c_t *i2c, dif_i2c_irq_t irq,
                               const bool val) {
  if (i2c == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t index;
  if (!i2c_get_irq_bit_index(irq, &index)) {
    return kDifBadArg;
  }

  uint32_t intr_test_reg = bitfield_bit32_write(0, index, val);
  mmio_region_write32(i2c->base_addr, (ptrdiff_t)I2C_INTR_TEST_REG_OFFSET,
                      intr_test_reg);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_irq_get_enabled(const dif_i2c_t *i2c, dif_i2c_irq_t irq,
                                     dif_toggle_t *state) {
  if (i2c == NULL || state == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t index;
  if (!i2c_get_irq_bit_index(irq, &index)) {
    return kDifBadArg;
  }

  uint32_t intr_enable_reg =
      mmio_region_read32(i2c->base_addr, (ptrdiff_t)I2C_INTR_ENABLE_REG_OFFSET);

  bool is_enabled = bitfield_bit32_read(intr_enable_reg, index);
  *state = is_enabled ? kDifToggleEnabled : kDifToggleDisabled;

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_irq_set_enabled(const dif_i2c_t *i2c, dif_i2c_irq_t irq,
                                     dif_toggle_t state) {
  if (i2c == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t index;
  if (!i2c_get_irq_bit_index(irq, &index)) {
    return kDifBadArg;
  }

  uint32_t intr_enable_reg =
      mmio_region_read32(i2c->base_addr, (ptrdiff_t)I2C_INTR_ENABLE_REG_OFFSET);

  bool enable_bit = (state == kDifToggleEnabled) ? true : false;
  intr_enable_reg = bitfield_bit32_write(intr_enable_reg, index, enable_bit);
  mmio_region_write32(i2c->base_addr, (ptrdiff_t)I2C_INTR_ENABLE_REG_OFFSET,
                      intr_enable_reg);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_irq_disable_all(const dif_i2c_t *i2c,
                                     dif_i2c_irq_enable_snapshot_t *snapshot) {
  if (i2c == NULL) {
    return kDifBadArg;
  }

  // Pass the current interrupt state to the caller, if requested.
  if (snapshot != NULL) {
    *snapshot = mmio_region_read32(i2c->base_addr,
                                   (ptrdiff_t)I2C_INTR_ENABLE_REG_OFFSET);
  }

  // Disable all interrupts.
  mmio_region_write32(i2c->base_addr, (ptrdiff_t)I2C_INTR_ENABLE_REG_OFFSET,
                      0u);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_irq_restore_all(
    const dif_i2c_t *i2c, const dif_i2c_irq_enable_snapshot_t *snapshot) {
  if (i2c == NULL || snapshot == NULL) {
    return kDifBadArg;
  }

  mmio_region_write32(i2c->base_addr, (ptrdiff_t)I2C_INTR_ENABLE_REG_OFFSET,
                      *snapshot);

  return kDifOk;
}
