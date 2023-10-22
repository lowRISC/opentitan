// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/ip/soc_proxy/dif/autogen/dif_soc_proxy_autogen.h"

#include <stdint.h>

#include "sw/ip/base/dif/dif_base.h"

#include "soc_proxy_regs.h"  // Generated.

OT_WARN_UNUSED_RESULT
dif_result_t dif_soc_proxy_init(mmio_region_t base_addr,
                                dif_soc_proxy_t *soc_proxy) {
  if (soc_proxy == NULL) {
    return kDifBadArg;
  }

  soc_proxy->base_addr = base_addr;

  return kDifOk;
}

dif_result_t dif_soc_proxy_alert_force(const dif_soc_proxy_t *soc_proxy,
                                       dif_soc_proxy_alert_t alert) {
  if (soc_proxy == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t alert_idx;
  switch (alert) {
    case kDifSocProxyAlertFatalAlertIntg:
      alert_idx = SOC_PROXY_ALERT_TEST_FATAL_ALERT_INTG_BIT;
      break;
    case kDifSocProxyAlertFatalAlertExternal0:
      alert_idx = SOC_PROXY_ALERT_TEST_FATAL_ALERT_EXTERNAL_0_BIT;
      break;
    case kDifSocProxyAlertFatalAlertExternal1:
      alert_idx = SOC_PROXY_ALERT_TEST_FATAL_ALERT_EXTERNAL_1_BIT;
      break;
    case kDifSocProxyAlertFatalAlertExternal2:
      alert_idx = SOC_PROXY_ALERT_TEST_FATAL_ALERT_EXTERNAL_2_BIT;
      break;
    case kDifSocProxyAlertFatalAlertExternal3:
      alert_idx = SOC_PROXY_ALERT_TEST_FATAL_ALERT_EXTERNAL_3_BIT;
      break;
    case kDifSocProxyAlertFatalAlertExternal4:
      alert_idx = SOC_PROXY_ALERT_TEST_FATAL_ALERT_EXTERNAL_4_BIT;
      break;
    case kDifSocProxyAlertFatalAlertExternal5:
      alert_idx = SOC_PROXY_ALERT_TEST_FATAL_ALERT_EXTERNAL_5_BIT;
      break;
    case kDifSocProxyAlertFatalAlertExternal6:
      alert_idx = SOC_PROXY_ALERT_TEST_FATAL_ALERT_EXTERNAL_6_BIT;
      break;
    case kDifSocProxyAlertFatalAlertExternal7:
      alert_idx = SOC_PROXY_ALERT_TEST_FATAL_ALERT_EXTERNAL_7_BIT;
      break;
    case kDifSocProxyAlertFatalAlertExternal8:
      alert_idx = SOC_PROXY_ALERT_TEST_FATAL_ALERT_EXTERNAL_8_BIT;
      break;
    case kDifSocProxyAlertFatalAlertExternal9:
      alert_idx = SOC_PROXY_ALERT_TEST_FATAL_ALERT_EXTERNAL_9_BIT;
      break;
    case kDifSocProxyAlertFatalAlertExternal10:
      alert_idx = SOC_PROXY_ALERT_TEST_FATAL_ALERT_EXTERNAL_10_BIT;
      break;
    case kDifSocProxyAlertFatalAlertExternal11:
      alert_idx = SOC_PROXY_ALERT_TEST_FATAL_ALERT_EXTERNAL_11_BIT;
      break;
    case kDifSocProxyAlertFatalAlertExternal12:
      alert_idx = SOC_PROXY_ALERT_TEST_FATAL_ALERT_EXTERNAL_12_BIT;
      break;
    case kDifSocProxyAlertFatalAlertExternal13:
      alert_idx = SOC_PROXY_ALERT_TEST_FATAL_ALERT_EXTERNAL_13_BIT;
      break;
    case kDifSocProxyAlertFatalAlertExternal14:
      alert_idx = SOC_PROXY_ALERT_TEST_FATAL_ALERT_EXTERNAL_14_BIT;
      break;
    case kDifSocProxyAlertFatalAlertExternal15:
      alert_idx = SOC_PROXY_ALERT_TEST_FATAL_ALERT_EXTERNAL_15_BIT;
      break;
    case kDifSocProxyAlertFatalAlertExternal16:
      alert_idx = SOC_PROXY_ALERT_TEST_FATAL_ALERT_EXTERNAL_16_BIT;
      break;
    case kDifSocProxyAlertFatalAlertExternal17:
      alert_idx = SOC_PROXY_ALERT_TEST_FATAL_ALERT_EXTERNAL_17_BIT;
      break;
    case kDifSocProxyAlertFatalAlertExternal18:
      alert_idx = SOC_PROXY_ALERT_TEST_FATAL_ALERT_EXTERNAL_18_BIT;
      break;
    case kDifSocProxyAlertFatalAlertExternal19:
      alert_idx = SOC_PROXY_ALERT_TEST_FATAL_ALERT_EXTERNAL_19_BIT;
      break;
    case kDifSocProxyAlertFatalAlertExternal20:
      alert_idx = SOC_PROXY_ALERT_TEST_FATAL_ALERT_EXTERNAL_20_BIT;
      break;
    case kDifSocProxyAlertFatalAlertExternal21:
      alert_idx = SOC_PROXY_ALERT_TEST_FATAL_ALERT_EXTERNAL_21_BIT;
      break;
    case kDifSocProxyAlertFatalAlertExternal22:
      alert_idx = SOC_PROXY_ALERT_TEST_FATAL_ALERT_EXTERNAL_22_BIT;
      break;
    case kDifSocProxyAlertFatalAlertExternal23:
      alert_idx = SOC_PROXY_ALERT_TEST_FATAL_ALERT_EXTERNAL_23_BIT;
      break;
    case kDifSocProxyAlertRecovAlertExternal0:
      alert_idx = SOC_PROXY_ALERT_TEST_RECOV_ALERT_EXTERNAL_0_BIT;
      break;
    case kDifSocProxyAlertRecovAlertExternal1:
      alert_idx = SOC_PROXY_ALERT_TEST_RECOV_ALERT_EXTERNAL_1_BIT;
      break;
    case kDifSocProxyAlertRecovAlertExternal2:
      alert_idx = SOC_PROXY_ALERT_TEST_RECOV_ALERT_EXTERNAL_2_BIT;
      break;
    case kDifSocProxyAlertRecovAlertExternal3:
      alert_idx = SOC_PROXY_ALERT_TEST_RECOV_ALERT_EXTERNAL_3_BIT;
      break;
    default:
      return kDifBadArg;
  }

  uint32_t alert_test_reg = bitfield_bit32_write(0, alert_idx, true);
  mmio_region_write32(soc_proxy->base_addr,
                      (ptrdiff_t)SOC_PROXY_ALERT_TEST_REG_OFFSET,
                      alert_test_reg);

  return kDifOk;
}

/**
 * Get the corresponding interrupt register bit offset of the IRQ.
 */
static bool soc_proxy_get_irq_bit_index(dif_soc_proxy_irq_t irq,
                                        bitfield_bit32_index_t *index_out) {
  switch (irq) {
    case kDifSocProxyIrqExternal0:
      *index_out = 0;
      break;
    case kDifSocProxyIrqExternal1:
      *index_out = 1;
      break;
    case kDifSocProxyIrqExternal2:
      *index_out = 2;
      break;
    case kDifSocProxyIrqExternal3:
      *index_out = 3;
      break;
    case kDifSocProxyIrqExternal4:
      *index_out = 4;
      break;
    case kDifSocProxyIrqExternal5:
      *index_out = 5;
      break;
    case kDifSocProxyIrqExternal6:
      *index_out = 6;
      break;
    case kDifSocProxyIrqExternal7:
      *index_out = 7;
      break;
    case kDifSocProxyIrqExternal8:
      *index_out = 8;
      break;
    case kDifSocProxyIrqExternal9:
      *index_out = 9;
      break;
    case kDifSocProxyIrqExternal10:
      *index_out = 10;
      break;
    case kDifSocProxyIrqExternal11:
      *index_out = 11;
      break;
    case kDifSocProxyIrqExternal12:
      *index_out = 12;
      break;
    case kDifSocProxyIrqExternal13:
      *index_out = 13;
      break;
    case kDifSocProxyIrqExternal14:
      *index_out = 14;
      break;
    case kDifSocProxyIrqExternal15:
      *index_out = 15;
      break;
    case kDifSocProxyIrqExternal16:
      *index_out = 16;
      break;
    case kDifSocProxyIrqExternal17:
      *index_out = 17;
      break;
    case kDifSocProxyIrqExternal18:
      *index_out = 18;
      break;
    case kDifSocProxyIrqExternal19:
      *index_out = 19;
      break;
    case kDifSocProxyIrqExternal20:
      *index_out = 20;
      break;
    case kDifSocProxyIrqExternal21:
      *index_out = 21;
      break;
    case kDifSocProxyIrqExternal22:
      *index_out = 22;
      break;
    case kDifSocProxyIrqExternal23:
      *index_out = 23;
      break;
    case kDifSocProxyIrqExternal24:
      *index_out = 24;
      break;
    case kDifSocProxyIrqExternal25:
      *index_out = 25;
      break;
    case kDifSocProxyIrqExternal26:
      *index_out = 26;
      break;
    case kDifSocProxyIrqExternal27:
      *index_out = 27;
      break;
    case kDifSocProxyIrqExternal28:
      *index_out = 28;
      break;
    case kDifSocProxyIrqExternal29:
      *index_out = 29;
      break;
    case kDifSocProxyIrqExternal30:
      *index_out = 30;
      break;
    case kDifSocProxyIrqExternal31:
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
dif_result_t dif_soc_proxy_irq_get_type(const dif_soc_proxy_t *soc_proxy,
                                        dif_soc_proxy_irq_t irq,
                                        dif_irq_type_t *type) {
  if (soc_proxy == NULL || type == NULL ||
      irq == kDifSocProxyIrqExternal31 + 1) {
    return kDifBadArg;
  }

  *type = irq_types[irq];

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_soc_proxy_irq_get_state(
    const dif_soc_proxy_t *soc_proxy,
    dif_soc_proxy_irq_state_snapshot_t *snapshot) {
  if (soc_proxy == NULL || snapshot == NULL) {
    return kDifBadArg;
  }

  *snapshot = mmio_region_read32(soc_proxy->base_addr,
                                 (ptrdiff_t)SOC_PROXY_INTR_STATE_REG_OFFSET);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_soc_proxy_irq_acknowledge_state(
    const dif_soc_proxy_t *soc_proxy,
    dif_soc_proxy_irq_state_snapshot_t snapshot) {
  if (soc_proxy == NULL) {
    return kDifBadArg;
  }

  mmio_region_write32(soc_proxy->base_addr,
                      (ptrdiff_t)SOC_PROXY_INTR_STATE_REG_OFFSET, snapshot);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_soc_proxy_irq_is_pending(const dif_soc_proxy_t *soc_proxy,
                                          dif_soc_proxy_irq_t irq,
                                          bool *is_pending) {
  if (soc_proxy == NULL || is_pending == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t index;
  if (!soc_proxy_get_irq_bit_index(irq, &index)) {
    return kDifBadArg;
  }

  uint32_t intr_state_reg = mmio_region_read32(
      soc_proxy->base_addr, (ptrdiff_t)SOC_PROXY_INTR_STATE_REG_OFFSET);

  *is_pending = bitfield_bit32_read(intr_state_reg, index);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_soc_proxy_irq_acknowledge_all(
    const dif_soc_proxy_t *soc_proxy) {
  if (soc_proxy == NULL) {
    return kDifBadArg;
  }

  // Writing to the register clears the corresponding bits (Write-one clear).
  mmio_region_write32(soc_proxy->base_addr,
                      (ptrdiff_t)SOC_PROXY_INTR_STATE_REG_OFFSET, UINT32_MAX);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_soc_proxy_irq_acknowledge(const dif_soc_proxy_t *soc_proxy,
                                           dif_soc_proxy_irq_t irq) {
  if (soc_proxy == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t index;
  if (!soc_proxy_get_irq_bit_index(irq, &index)) {
    return kDifBadArg;
  }

  // Writing to the register clears the corresponding bits (Write-one clear).
  uint32_t intr_state_reg = bitfield_bit32_write(0, index, true);
  mmio_region_write32(soc_proxy->base_addr,
                      (ptrdiff_t)SOC_PROXY_INTR_STATE_REG_OFFSET,
                      intr_state_reg);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_soc_proxy_irq_force(const dif_soc_proxy_t *soc_proxy,
                                     dif_soc_proxy_irq_t irq, const bool val) {
  if (soc_proxy == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t index;
  if (!soc_proxy_get_irq_bit_index(irq, &index)) {
    return kDifBadArg;
  }

  uint32_t intr_test_reg = bitfield_bit32_write(0, index, val);
  mmio_region_write32(soc_proxy->base_addr,
                      (ptrdiff_t)SOC_PROXY_INTR_TEST_REG_OFFSET, intr_test_reg);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_soc_proxy_irq_get_enabled(const dif_soc_proxy_t *soc_proxy,
                                           dif_soc_proxy_irq_t irq,
                                           dif_toggle_t *state) {
  if (soc_proxy == NULL || state == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t index;
  if (!soc_proxy_get_irq_bit_index(irq, &index)) {
    return kDifBadArg;
  }

  uint32_t intr_enable_reg = mmio_region_read32(
      soc_proxy->base_addr, (ptrdiff_t)SOC_PROXY_INTR_ENABLE_REG_OFFSET);

  bool is_enabled = bitfield_bit32_read(intr_enable_reg, index);
  *state = is_enabled ? kDifToggleEnabled : kDifToggleDisabled;

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_soc_proxy_irq_set_enabled(const dif_soc_proxy_t *soc_proxy,
                                           dif_soc_proxy_irq_t irq,
                                           dif_toggle_t state) {
  if (soc_proxy == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t index;
  if (!soc_proxy_get_irq_bit_index(irq, &index)) {
    return kDifBadArg;
  }

  uint32_t intr_enable_reg = mmio_region_read32(
      soc_proxy->base_addr, (ptrdiff_t)SOC_PROXY_INTR_ENABLE_REG_OFFSET);

  bool enable_bit = (state == kDifToggleEnabled) ? true : false;
  intr_enable_reg = bitfield_bit32_write(intr_enable_reg, index, enable_bit);
  mmio_region_write32(soc_proxy->base_addr,
                      (ptrdiff_t)SOC_PROXY_INTR_ENABLE_REG_OFFSET,
                      intr_enable_reg);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_soc_proxy_irq_disable_all(
    const dif_soc_proxy_t *soc_proxy,
    dif_soc_proxy_irq_enable_snapshot_t *snapshot) {
  if (soc_proxy == NULL) {
    return kDifBadArg;
  }

  // Pass the current interrupt state to the caller, if requested.
  if (snapshot != NULL) {
    *snapshot = mmio_region_read32(soc_proxy->base_addr,
                                   (ptrdiff_t)SOC_PROXY_INTR_ENABLE_REG_OFFSET);
  }

  // Disable all interrupts.
  mmio_region_write32(soc_proxy->base_addr,
                      (ptrdiff_t)SOC_PROXY_INTR_ENABLE_REG_OFFSET, 0u);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_soc_proxy_irq_restore_all(
    const dif_soc_proxy_t *soc_proxy,
    const dif_soc_proxy_irq_enable_snapshot_t *snapshot) {
  if (soc_proxy == NULL || snapshot == NULL) {
    return kDifBadArg;
  }

  mmio_region_write32(soc_proxy->base_addr,
                      (ptrdiff_t)SOC_PROXY_INTR_ENABLE_REG_OFFSET, *snapshot);

  return kDifOk;
}
