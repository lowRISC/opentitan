// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/device/lib/dif/autogen/dif_aon_timer_autogen.h"

#include <assert.h>
#include <stdint.h>

#include "sw/device/lib/dif/dif_base.h"

#include "aon_timer_regs.h"  // Generated.

static_assert(AON_TIMER_INTR_STATE_WKUP_TIMER_EXPIRED_BIT ==
                  AON_TIMER_INTR_TEST_WKUP_TIMER_EXPIRED_BIT,
              "Expected IRQ bit offsets to match across STATE/TEST regs.");
static_assert(AON_TIMER_INTR_STATE_WDOG_TIMER_BARK_BIT ==
                  AON_TIMER_INTR_TEST_WDOG_TIMER_BARK_BIT,
              "Expected IRQ bit offsets to match across STATE/TEST regs.");

OT_WARN_UNUSED_RESULT
dif_result_t dif_aon_timer_init(mmio_region_t base_addr,
                                dif_aon_timer_t *aon_timer) {
  if (aon_timer == NULL) {
    return kDifBadArg;
  }

  aon_timer->base_addr = base_addr;

  return kDifOk;
}

dif_result_t dif_aon_timer_alert_force(const dif_aon_timer_t *aon_timer,
                                       dif_aon_timer_alert_t alert) {
  if (aon_timer == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t alert_idx;
  switch (alert) {
    case kDifAonTimerAlertFatalFault:
      alert_idx = AON_TIMER_ALERT_TEST_FATAL_FAULT_BIT;
      break;
    default:
      return kDifBadArg;
  }

  uint32_t alert_test_reg = bitfield_bit32_write(0, alert_idx, true);
  mmio_region_write32(aon_timer->base_addr,
                      (ptrdiff_t)AON_TIMER_ALERT_TEST_REG_OFFSET,
                      alert_test_reg);

  return kDifOk;
}

/**
 * Get the corresponding interrupt register bit offset of the IRQ.
 */
static bool aon_timer_get_irq_bit_index(dif_aon_timer_irq_t irq,
                                        bitfield_bit32_index_t *index_out) {
  switch (irq) {
    case kDifAonTimerIrqWkupTimerExpired:
      *index_out = AON_TIMER_INTR_STATE_WKUP_TIMER_EXPIRED_BIT;
      break;
    case kDifAonTimerIrqWdogTimerBark:
      *index_out = AON_TIMER_INTR_STATE_WDOG_TIMER_BARK_BIT;
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
dif_result_t dif_aon_timer_irq_get_type(const dif_aon_timer_t *aon_timer,
                                        dif_aon_timer_irq_t irq,
                                        dif_irq_type_t *type) {
  if (aon_timer == NULL || type == NULL ||
      irq == kDifAonTimerIrqWdogTimerBark + 1) {
    return kDifBadArg;
  }

  *type = irq_types[irq];

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_aon_timer_irq_get_state(
    const dif_aon_timer_t *aon_timer,
    dif_aon_timer_irq_state_snapshot_t *snapshot) {
  if (aon_timer == NULL || snapshot == NULL) {
    return kDifBadArg;
  }

  *snapshot = mmio_region_read32(aon_timer->base_addr,
                                 (ptrdiff_t)AON_TIMER_INTR_STATE_REG_OFFSET);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_aon_timer_irq_acknowledge_state(
    const dif_aon_timer_t *aon_timer,
    dif_aon_timer_irq_state_snapshot_t snapshot) {
  if (aon_timer == NULL) {
    return kDifBadArg;
  }

  mmio_region_write32(aon_timer->base_addr,
                      (ptrdiff_t)AON_TIMER_INTR_STATE_REG_OFFSET, snapshot);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_aon_timer_irq_is_pending(const dif_aon_timer_t *aon_timer,
                                          dif_aon_timer_irq_t irq,
                                          bool *is_pending) {
  if (aon_timer == NULL || is_pending == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t index;
  if (!aon_timer_get_irq_bit_index(irq, &index)) {
    return kDifBadArg;
  }

  uint32_t intr_state_reg = mmio_region_read32(
      aon_timer->base_addr, (ptrdiff_t)AON_TIMER_INTR_STATE_REG_OFFSET);

  *is_pending = bitfield_bit32_read(intr_state_reg, index);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_aon_timer_irq_acknowledge_all(
    const dif_aon_timer_t *aon_timer) {
  if (aon_timer == NULL) {
    return kDifBadArg;
  }

  // Writing to the register clears the corresponding bits (Write-one clear).
  mmio_region_write32(aon_timer->base_addr,
                      (ptrdiff_t)AON_TIMER_INTR_STATE_REG_OFFSET, UINT32_MAX);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_aon_timer_irq_acknowledge(const dif_aon_timer_t *aon_timer,
                                           dif_aon_timer_irq_t irq) {
  if (aon_timer == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t index;
  if (!aon_timer_get_irq_bit_index(irq, &index)) {
    return kDifBadArg;
  }

  // Writing to the register clears the corresponding bits (Write-one clear).
  uint32_t intr_state_reg = bitfield_bit32_write(0, index, true);
  mmio_region_write32(aon_timer->base_addr,
                      (ptrdiff_t)AON_TIMER_INTR_STATE_REG_OFFSET,
                      intr_state_reg);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_aon_timer_irq_force(const dif_aon_timer_t *aon_timer,
                                     dif_aon_timer_irq_t irq, const bool val) {
  if (aon_timer == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t index;
  if (!aon_timer_get_irq_bit_index(irq, &index)) {
    return kDifBadArg;
  }

  uint32_t intr_test_reg = bitfield_bit32_write(0, index, val);
  mmio_region_write32(aon_timer->base_addr,
                      (ptrdiff_t)AON_TIMER_INTR_TEST_REG_OFFSET, intr_test_reg);

  return kDifOk;
}
