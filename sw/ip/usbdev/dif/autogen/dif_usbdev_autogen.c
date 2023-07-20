// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/device/lib/dif/autogen/dif_usbdev_autogen.h"

#include <stdint.h>

#include "sw/device/lib/dif/dif_base.h"

#include "usbdev_regs.h"  // Generated.

OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_init(mmio_region_t base_addr, dif_usbdev_t *usbdev) {
  if (usbdev == NULL) {
    return kDifBadArg;
  }

  usbdev->base_addr = base_addr;

  return kDifOk;
}

dif_result_t dif_usbdev_alert_force(const dif_usbdev_t *usbdev,
                                    dif_usbdev_alert_t alert) {
  if (usbdev == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t alert_idx;
  switch (alert) {
    case kDifUsbdevAlertFatalFault:
      alert_idx = USBDEV_ALERT_TEST_FATAL_FAULT_BIT;
      break;
    default:
      return kDifBadArg;
  }

  uint32_t alert_test_reg = bitfield_bit32_write(0, alert_idx, true);
  mmio_region_write32(usbdev->base_addr,
                      (ptrdiff_t)USBDEV_ALERT_TEST_REG_OFFSET, alert_test_reg);

  return kDifOk;
}

/**
 * Get the corresponding interrupt register bit offset of the IRQ.
 */
static bool usbdev_get_irq_bit_index(dif_usbdev_irq_t irq,
                                     bitfield_bit32_index_t *index_out) {
  switch (irq) {
    case kDifUsbdevIrqPktReceived:
      *index_out = USBDEV_INTR_COMMON_PKT_RECEIVED_BIT;
      break;
    case kDifUsbdevIrqPktSent:
      *index_out = USBDEV_INTR_COMMON_PKT_SENT_BIT;
      break;
    case kDifUsbdevIrqDisconnected:
      *index_out = USBDEV_INTR_COMMON_DISCONNECTED_BIT;
      break;
    case kDifUsbdevIrqHostLost:
      *index_out = USBDEV_INTR_COMMON_HOST_LOST_BIT;
      break;
    case kDifUsbdevIrqLinkReset:
      *index_out = USBDEV_INTR_COMMON_LINK_RESET_BIT;
      break;
    case kDifUsbdevIrqLinkSuspend:
      *index_out = USBDEV_INTR_COMMON_LINK_SUSPEND_BIT;
      break;
    case kDifUsbdevIrqLinkResume:
      *index_out = USBDEV_INTR_COMMON_LINK_RESUME_BIT;
      break;
    case kDifUsbdevIrqAvEmpty:
      *index_out = USBDEV_INTR_COMMON_AV_EMPTY_BIT;
      break;
    case kDifUsbdevIrqRxFull:
      *index_out = USBDEV_INTR_COMMON_RX_FULL_BIT;
      break;
    case kDifUsbdevIrqAvOverflow:
      *index_out = USBDEV_INTR_COMMON_AV_OVERFLOW_BIT;
      break;
    case kDifUsbdevIrqLinkInErr:
      *index_out = USBDEV_INTR_COMMON_LINK_IN_ERR_BIT;
      break;
    case kDifUsbdevIrqRxCrcErr:
      *index_out = USBDEV_INTR_COMMON_RX_CRC_ERR_BIT;
      break;
    case kDifUsbdevIrqRxPidErr:
      *index_out = USBDEV_INTR_COMMON_RX_PID_ERR_BIT;
      break;
    case kDifUsbdevIrqRxBitstuffErr:
      *index_out = USBDEV_INTR_COMMON_RX_BITSTUFF_ERR_BIT;
      break;
    case kDifUsbdevIrqFrame:
      *index_out = USBDEV_INTR_COMMON_FRAME_BIT;
      break;
    case kDifUsbdevIrqPowered:
      *index_out = USBDEV_INTR_COMMON_POWERED_BIT;
      break;
    case kDifUsbdevIrqLinkOutErr:
      *index_out = USBDEV_INTR_COMMON_LINK_OUT_ERR_BIT;
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
    kDifIrqTypeEvent,
};

OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_irq_get_type(const dif_usbdev_t *usbdev,
                                     dif_usbdev_irq_t irq,
                                     dif_irq_type_t *type) {
  if (usbdev == NULL || type == NULL || irq == kDifUsbdevIrqLinkOutErr + 1) {
    return kDifBadArg;
  }

  *type = irq_types[irq];

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_irq_get_state(
    const dif_usbdev_t *usbdev, dif_usbdev_irq_state_snapshot_t *snapshot) {
  if (usbdev == NULL || snapshot == NULL) {
    return kDifBadArg;
  }

  *snapshot = mmio_region_read32(usbdev->base_addr,
                                 (ptrdiff_t)USBDEV_INTR_STATE_REG_OFFSET);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_irq_acknowledge_state(
    const dif_usbdev_t *usbdev, dif_usbdev_irq_state_snapshot_t snapshot) {
  if (usbdev == NULL) {
    return kDifBadArg;
  }

  mmio_region_write32(usbdev->base_addr,
                      (ptrdiff_t)USBDEV_INTR_STATE_REG_OFFSET, snapshot);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_irq_is_pending(const dif_usbdev_t *usbdev,
                                       dif_usbdev_irq_t irq, bool *is_pending) {
  if (usbdev == NULL || is_pending == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t index;
  if (!usbdev_get_irq_bit_index(irq, &index)) {
    return kDifBadArg;
  }

  uint32_t intr_state_reg = mmio_region_read32(
      usbdev->base_addr, (ptrdiff_t)USBDEV_INTR_STATE_REG_OFFSET);

  *is_pending = bitfield_bit32_read(intr_state_reg, index);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_irq_acknowledge_all(const dif_usbdev_t *usbdev) {
  if (usbdev == NULL) {
    return kDifBadArg;
  }

  // Writing to the register clears the corresponding bits (Write-one clear).
  mmio_region_write32(usbdev->base_addr,
                      (ptrdiff_t)USBDEV_INTR_STATE_REG_OFFSET, UINT32_MAX);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_irq_acknowledge(const dif_usbdev_t *usbdev,
                                        dif_usbdev_irq_t irq) {
  if (usbdev == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t index;
  if (!usbdev_get_irq_bit_index(irq, &index)) {
    return kDifBadArg;
  }

  // Writing to the register clears the corresponding bits (Write-one clear).
  uint32_t intr_state_reg = bitfield_bit32_write(0, index, true);
  mmio_region_write32(usbdev->base_addr,
                      (ptrdiff_t)USBDEV_INTR_STATE_REG_OFFSET, intr_state_reg);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_irq_force(const dif_usbdev_t *usbdev,
                                  dif_usbdev_irq_t irq, const bool val) {
  if (usbdev == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t index;
  if (!usbdev_get_irq_bit_index(irq, &index)) {
    return kDifBadArg;
  }

  uint32_t intr_test_reg = bitfield_bit32_write(0, index, val);
  mmio_region_write32(usbdev->base_addr, (ptrdiff_t)USBDEV_INTR_TEST_REG_OFFSET,
                      intr_test_reg);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_irq_get_enabled(const dif_usbdev_t *usbdev,
                                        dif_usbdev_irq_t irq,
                                        dif_toggle_t *state) {
  if (usbdev == NULL || state == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t index;
  if (!usbdev_get_irq_bit_index(irq, &index)) {
    return kDifBadArg;
  }

  uint32_t intr_enable_reg = mmio_region_read32(
      usbdev->base_addr, (ptrdiff_t)USBDEV_INTR_ENABLE_REG_OFFSET);

  bool is_enabled = bitfield_bit32_read(intr_enable_reg, index);
  *state = is_enabled ? kDifToggleEnabled : kDifToggleDisabled;

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_irq_set_enabled(const dif_usbdev_t *usbdev,
                                        dif_usbdev_irq_t irq,
                                        dif_toggle_t state) {
  if (usbdev == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t index;
  if (!usbdev_get_irq_bit_index(irq, &index)) {
    return kDifBadArg;
  }

  uint32_t intr_enable_reg = mmio_region_read32(
      usbdev->base_addr, (ptrdiff_t)USBDEV_INTR_ENABLE_REG_OFFSET);

  bool enable_bit = (state == kDifToggleEnabled) ? true : false;
  intr_enable_reg = bitfield_bit32_write(intr_enable_reg, index, enable_bit);
  mmio_region_write32(usbdev->base_addr,
                      (ptrdiff_t)USBDEV_INTR_ENABLE_REG_OFFSET,
                      intr_enable_reg);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_irq_disable_all(
    const dif_usbdev_t *usbdev, dif_usbdev_irq_enable_snapshot_t *snapshot) {
  if (usbdev == NULL) {
    return kDifBadArg;
  }

  // Pass the current interrupt state to the caller, if requested.
  if (snapshot != NULL) {
    *snapshot = mmio_region_read32(usbdev->base_addr,
                                   (ptrdiff_t)USBDEV_INTR_ENABLE_REG_OFFSET);
  }

  // Disable all interrupts.
  mmio_region_write32(usbdev->base_addr,
                      (ptrdiff_t)USBDEV_INTR_ENABLE_REG_OFFSET, 0u);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_irq_restore_all(
    const dif_usbdev_t *usbdev,
    const dif_usbdev_irq_enable_snapshot_t *snapshot) {
  if (usbdev == NULL || snapshot == NULL) {
    return kDifBadArg;
  }

  mmio_region_write32(usbdev->base_addr,
                      (ptrdiff_t)USBDEV_INTR_ENABLE_REG_OFFSET, *snapshot);

  return kDifOk;
}
