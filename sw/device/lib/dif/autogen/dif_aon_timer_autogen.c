// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This file is auto-generated.

#include "sw/device/lib/dif/dif_aon_timer.h"

#include "aon_timer_regs.h"  // Generated.

/**
 * Get the corresponding interrupt register bit offset. INTR_STATE,
 * INTR_ENABLE and INTR_TEST registers have the same bit offsets, so this
 * routine can be reused.
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

OT_WARN_UNUSED_RESULT
dif_result_t dif_aon_timer_irq_get_state(
    const dif_aon_timer_t *aon_timer,
    dif_aon_timer_irq_state_snapshot_t *snapshot) {
  if (aon_timer == NULL || snapshot == NULL) {
    return kDifBadArg;
  }

  *snapshot =
      mmio_region_read32(aon_timer->base_addr, AON_TIMER_INTR_STATE_REG_OFFSET);

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

  uint32_t intr_state_reg =
      mmio_region_read32(aon_timer->base_addr, AON_TIMER_INTR_STATE_REG_OFFSET);

  *is_pending = bitfield_bit32_read(intr_state_reg, index);

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
  mmio_region_write32(aon_timer->base_addr, AON_TIMER_INTR_STATE_REG_OFFSET,
                      intr_state_reg);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_aon_timer_irq_force(const dif_aon_timer_t *aon_timer,
                                     dif_aon_timer_irq_t irq) {
  if (aon_timer == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t index;
  if (!aon_timer_get_irq_bit_index(irq, &index)) {
    return kDifBadArg;
  }

  uint32_t intr_test_reg = bitfield_bit32_write(0, index, true);
  mmio_region_write32(aon_timer->base_addr, AON_TIMER_INTR_TEST_REG_OFFSET,
                      intr_test_reg);

  return kDifOk;
}
