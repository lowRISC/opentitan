// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/device/lib/dif/autogen/dif_gpio_autogen.h"

#include <stdint.h>

#include "sw/device/lib/dif/dif_base.h"

#include "gpio_regs.h"  // Generated.

OT_WARN_UNUSED_RESULT
dif_result_t dif_gpio_init(mmio_region_t base_addr, dif_gpio_t *gpio) {
  if (gpio == NULL) {
    return kDifBadArg;
  }

  gpio->base_addr = base_addr;

  return kDifOk;
}

dif_result_t dif_gpio_alert_force(const dif_gpio_t *gpio,
                                  dif_gpio_alert_t alert) {
  if (gpio == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t alert_idx;
  switch (alert) {
    case kDifGpioAlertFatalFault:
      alert_idx = GPIO_ALERT_TEST_FATAL_FAULT_BIT;
      break;
    default:
      return kDifBadArg;
  }

  uint32_t alert_test_reg = bitfield_bit32_write(0, alert_idx, true);
  mmio_region_write32(gpio->base_addr, (ptrdiff_t)GPIO_ALERT_TEST_REG_OFFSET,
                      alert_test_reg);

  return kDifOk;
}

/**
 * Get the corresponding interrupt register bit offset of the IRQ.
 */
static bool gpio_get_irq_bit_index(dif_gpio_irq_t irq,
                                   bitfield_bit32_index_t *index_out) {
  switch (irq) {
    case kDifGpioIrqGpio0:
      *index_out = 0;
      break;
    case kDifGpioIrqGpio1:
      *index_out = 1;
      break;
    case kDifGpioIrqGpio2:
      *index_out = 2;
      break;
    case kDifGpioIrqGpio3:
      *index_out = 3;
      break;
    case kDifGpioIrqGpio4:
      *index_out = 4;
      break;
    case kDifGpioIrqGpio5:
      *index_out = 5;
      break;
    case kDifGpioIrqGpio6:
      *index_out = 6;
      break;
    case kDifGpioIrqGpio7:
      *index_out = 7;
      break;
    case kDifGpioIrqGpio8:
      *index_out = 8;
      break;
    case kDifGpioIrqGpio9:
      *index_out = 9;
      break;
    case kDifGpioIrqGpio10:
      *index_out = 10;
      break;
    case kDifGpioIrqGpio11:
      *index_out = 11;
      break;
    case kDifGpioIrqGpio12:
      *index_out = 12;
      break;
    case kDifGpioIrqGpio13:
      *index_out = 13;
      break;
    case kDifGpioIrqGpio14:
      *index_out = 14;
      break;
    case kDifGpioIrqGpio15:
      *index_out = 15;
      break;
    case kDifGpioIrqGpio16:
      *index_out = 16;
      break;
    case kDifGpioIrqGpio17:
      *index_out = 17;
      break;
    case kDifGpioIrqGpio18:
      *index_out = 18;
      break;
    case kDifGpioIrqGpio19:
      *index_out = 19;
      break;
    case kDifGpioIrqGpio20:
      *index_out = 20;
      break;
    case kDifGpioIrqGpio21:
      *index_out = 21;
      break;
    case kDifGpioIrqGpio22:
      *index_out = 22;
      break;
    case kDifGpioIrqGpio23:
      *index_out = 23;
      break;
    case kDifGpioIrqGpio24:
      *index_out = 24;
      break;
    case kDifGpioIrqGpio25:
      *index_out = 25;
      break;
    case kDifGpioIrqGpio26:
      *index_out = 26;
      break;
    case kDifGpioIrqGpio27:
      *index_out = 27;
      break;
    case kDifGpioIrqGpio28:
      *index_out = 28;
      break;
    case kDifGpioIrqGpio29:
      *index_out = 29;
      break;
    case kDifGpioIrqGpio30:
      *index_out = 30;
      break;
    case kDifGpioIrqGpio31:
      *index_out = 31;
      break;
    default:
      return false;
  }

  return true;
}

static dif_irq_type_t irq_types[] = {
    kDifIrqTypeEvent, kDifIrqTypeEvent, kDifIrqTypeEvent, kDifIrqTypeEvent,
    kDifIrqTypeEvent, kDifIrqTypeEvent, kDifIrqTypeEvent, kDifIrqTypeEvent,
    kDifIrqTypeEvent, kDifIrqTypeEvent, kDifIrqTypeEvent, kDifIrqTypeEvent,
    kDifIrqTypeEvent, kDifIrqTypeEvent, kDifIrqTypeEvent, kDifIrqTypeEvent,
    kDifIrqTypeEvent, kDifIrqTypeEvent, kDifIrqTypeEvent, kDifIrqTypeEvent,
    kDifIrqTypeEvent, kDifIrqTypeEvent, kDifIrqTypeEvent, kDifIrqTypeEvent,
    kDifIrqTypeEvent, kDifIrqTypeEvent, kDifIrqTypeEvent, kDifIrqTypeEvent,
    kDifIrqTypeEvent, kDifIrqTypeEvent, kDifIrqTypeEvent, kDifIrqTypeEvent,
};

OT_WARN_UNUSED_RESULT
dif_result_t dif_gpio_irq_get_type(const dif_gpio_t *gpio, dif_gpio_irq_t irq,
                                   dif_irq_type_t *type) {
  if (gpio == NULL || type == NULL || irq == kDifGpioIrqGpio31 + 1) {
    return kDifBadArg;
  }

  *type = irq_types[irq];

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_gpio_irq_get_state(const dif_gpio_t *gpio,
                                    dif_gpio_irq_state_snapshot_t *snapshot) {
  if (gpio == NULL || snapshot == NULL) {
    return kDifBadArg;
  }

  *snapshot = mmio_region_read32(gpio->base_addr,
                                 (ptrdiff_t)GPIO_INTR_STATE_REG_OFFSET);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_gpio_irq_acknowledge_state(
    const dif_gpio_t *gpio, dif_gpio_irq_state_snapshot_t snapshot) {
  if (gpio == NULL) {
    return kDifBadArg;
  }

  mmio_region_write32(gpio->base_addr, (ptrdiff_t)GPIO_INTR_STATE_REG_OFFSET,
                      snapshot);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_gpio_irq_is_pending(const dif_gpio_t *gpio, dif_gpio_irq_t irq,
                                     bool *is_pending) {
  if (gpio == NULL || is_pending == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t index;
  if (!gpio_get_irq_bit_index(irq, &index)) {
    return kDifBadArg;
  }

  uint32_t intr_state_reg = mmio_region_read32(
      gpio->base_addr, (ptrdiff_t)GPIO_INTR_STATE_REG_OFFSET);

  *is_pending = bitfield_bit32_read(intr_state_reg, index);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_gpio_irq_acknowledge_all(const dif_gpio_t *gpio) {
  if (gpio == NULL) {
    return kDifBadArg;
  }

  // Writing to the register clears the corresponding bits (Write-one clear).
  mmio_region_write32(gpio->base_addr, (ptrdiff_t)GPIO_INTR_STATE_REG_OFFSET,
                      UINT32_MAX);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_gpio_irq_acknowledge(const dif_gpio_t *gpio,
                                      dif_gpio_irq_t irq) {
  if (gpio == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t index;
  if (!gpio_get_irq_bit_index(irq, &index)) {
    return kDifBadArg;
  }

  // Writing to the register clears the corresponding bits (Write-one clear).
  uint32_t intr_state_reg = bitfield_bit32_write(0, index, true);
  mmio_region_write32(gpio->base_addr, (ptrdiff_t)GPIO_INTR_STATE_REG_OFFSET,
                      intr_state_reg);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_gpio_irq_force(const dif_gpio_t *gpio, dif_gpio_irq_t irq,
                                const bool val) {
  if (gpio == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t index;
  if (!gpio_get_irq_bit_index(irq, &index)) {
    return kDifBadArg;
  }

  uint32_t intr_test_reg = bitfield_bit32_write(0, index, val);
  mmio_region_write32(gpio->base_addr, (ptrdiff_t)GPIO_INTR_TEST_REG_OFFSET,
                      intr_test_reg);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_gpio_irq_get_enabled(const dif_gpio_t *gpio,
                                      dif_gpio_irq_t irq, dif_toggle_t *state) {
  if (gpio == NULL || state == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t index;
  if (!gpio_get_irq_bit_index(irq, &index)) {
    return kDifBadArg;
  }

  uint32_t intr_enable_reg = mmio_region_read32(
      gpio->base_addr, (ptrdiff_t)GPIO_INTR_ENABLE_REG_OFFSET);

  bool is_enabled = bitfield_bit32_read(intr_enable_reg, index);
  *state = is_enabled ? kDifToggleEnabled : kDifToggleDisabled;

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_gpio_irq_set_enabled(const dif_gpio_t *gpio,
                                      dif_gpio_irq_t irq, dif_toggle_t state) {
  if (gpio == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t index;
  if (!gpio_get_irq_bit_index(irq, &index)) {
    return kDifBadArg;
  }

  uint32_t intr_enable_reg = mmio_region_read32(
      gpio->base_addr, (ptrdiff_t)GPIO_INTR_ENABLE_REG_OFFSET);

  bool enable_bit = (state == kDifToggleEnabled) ? true : false;
  intr_enable_reg = bitfield_bit32_write(intr_enable_reg, index, enable_bit);
  mmio_region_write32(gpio->base_addr, (ptrdiff_t)GPIO_INTR_ENABLE_REG_OFFSET,
                      intr_enable_reg);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_gpio_irq_disable_all(
    const dif_gpio_t *gpio, dif_gpio_irq_enable_snapshot_t *snapshot) {
  if (gpio == NULL) {
    return kDifBadArg;
  }

  // Pass the current interrupt state to the caller, if requested.
  if (snapshot != NULL) {
    *snapshot = mmio_region_read32(gpio->base_addr,
                                   (ptrdiff_t)GPIO_INTR_ENABLE_REG_OFFSET);
  }

  // Disable all interrupts.
  mmio_region_write32(gpio->base_addr, (ptrdiff_t)GPIO_INTR_ENABLE_REG_OFFSET,
                      0u);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_gpio_irq_restore_all(
    const dif_gpio_t *gpio, const dif_gpio_irq_enable_snapshot_t *snapshot) {
  if (gpio == NULL || snapshot == NULL) {
    return kDifBadArg;
  }

  mmio_region_write32(gpio->base_addr, (ptrdiff_t)GPIO_INTR_ENABLE_REG_OFFSET,
                      *snapshot);

  return kDifOk;
}
