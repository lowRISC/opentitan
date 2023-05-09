// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/device/lib/dif/autogen/dif_rv_timer_autogen.h"

#include <assert.h>
#include <stdint.h>

#include "sw/device/lib/dif/dif_base.h"

#include "rv_timer_regs.h"  // Generated.

static_assert(RV_TIMER_INTR_STATE0_IS_0_BIT == RV_TIMER_INTR_ENABLE0_IE_0_BIT,
              "Expected IRQ bit offsets to match across STATE/ENABLE regs.");
static_assert(RV_TIMER_INTR_STATE0_IS_0_BIT == RV_TIMER_INTR_TEST0_T_0_BIT,
              "Expected IRQ bit offsets to match across STATE/ENABLE regs.");

OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_timer_init(mmio_region_t base_addr,
                               dif_rv_timer_t *rv_timer) {
  if (rv_timer == NULL) {
    return kDifBadArg;
  }

  rv_timer->base_addr = base_addr;

  return kDifOk;
}

dif_result_t dif_rv_timer_alert_force(const dif_rv_timer_t *rv_timer,
                                      dif_rv_timer_alert_t alert) {
  if (rv_timer == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t alert_idx;
  switch (alert) {
    case kDifRvTimerAlertFatalFault:
      alert_idx = RV_TIMER_ALERT_TEST_FATAL_FAULT_BIT;
      break;
    default:
      return kDifBadArg;
  }

  uint32_t alert_test_reg = bitfield_bit32_write(0, alert_idx, true);
  mmio_region_write32(rv_timer->base_addr,
                      (ptrdiff_t)RV_TIMER_ALERT_TEST_REG_OFFSET,
                      alert_test_reg);

  return kDifOk;
}

typedef enum dif_rv_timer_intr_reg {
  kDifRvTimerIntrRegState = 0,
  kDifRvTimerIntrRegEnable = 1,
  kDifRvTimerIntrRegTest = 2,
} dif_rv_timer_intr_reg_t;

static bool rv_timer_get_irq_reg_offset(dif_rv_timer_intr_reg_t intr_reg,
                                        dif_rv_timer_irq_t irq,
                                        uint32_t *intr_reg_offset) {
  switch (intr_reg) {
    case kDifRvTimerIntrRegState:
      switch (irq) {
        case kDifRvTimerIrqTimerExpiredHart0Timer0:
          *intr_reg_offset = RV_TIMER_INTR_STATE0_REG_OFFSET;
          break;
        default:
          return false;
      }
      break;
    case kDifRvTimerIntrRegEnable:
      switch (irq) {
        case kDifRvTimerIrqTimerExpiredHart0Timer0:
          *intr_reg_offset = RV_TIMER_INTR_ENABLE0_REG_OFFSET;
          break;
        default:
          return false;
      }
      break;
    case kDifRvTimerIntrRegTest:
      switch (irq) {
        case kDifRvTimerIrqTimerExpiredHart0Timer0:
          *intr_reg_offset = RV_TIMER_INTR_TEST0_REG_OFFSET;
          break;
        default:
          return false;
      }
      break;
    default:
      return false;
  }

  return true;
}

/**
 * Get the corresponding interrupt register bit offset of the IRQ.
 */
static bool rv_timer_get_irq_bit_index(dif_rv_timer_irq_t irq,
                                       bitfield_bit32_index_t *index_out) {
  switch (irq) {
    case kDifRvTimerIrqTimerExpiredHart0Timer0:
      *index_out = RV_TIMER_INTR_STATE0_IS_0_BIT;
      break;
    default:
      return false;
  }

  return true;
}

static dif_irq_type_t irq_types[] = {
    kDifIrqTypeEvent,
};

OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_timer_irq_get_type(const dif_rv_timer_t *rv_timer,
                                       dif_rv_timer_irq_t irq,
                                       dif_irq_type_t *type) {
  if (rv_timer == NULL || type == NULL ||
      irq == kDifRvTimerIrqTimerExpiredHart0Timer0 + 1) {
    return kDifBadArg;
  }

  *type = irq_types[irq];

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_timer_irq_get_state(
    const dif_rv_timer_t *rv_timer, uint32_t hart_id,
    dif_rv_timer_irq_state_snapshot_t *snapshot) {
  if (rv_timer == NULL || snapshot == NULL) {
    return kDifBadArg;
  }

  switch (hart_id) {
    case 0:
      *snapshot = mmio_region_read32(
          rv_timer->base_addr, (ptrdiff_t)RV_TIMER_INTR_STATE0_REG_OFFSET);

      break;
    default:
      return kDifBadArg;
  }

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_timer_irq_acknowledge_state(
    const dif_rv_timer_t *rv_timer, uint32_t hart_id,
    dif_rv_timer_irq_state_snapshot_t snapshot) {
  if (rv_timer == NULL) {
    return kDifBadArg;
  }

  switch (hart_id) {
    case 0:
      mmio_region_write32(rv_timer->base_addr,
                          (ptrdiff_t)RV_TIMER_INTR_STATE0_REG_OFFSET, snapshot);

      break;
    default:
      return kDifBadArg;
  }

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_timer_irq_is_pending(const dif_rv_timer_t *rv_timer,
                                         dif_rv_timer_irq_t irq,
                                         bool *is_pending) {
  if (rv_timer == NULL || is_pending == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t index;
  if (!rv_timer_get_irq_bit_index(irq, &index)) {
    return kDifBadArg;
  }

  uint32_t reg_offset = 0;
  if (!rv_timer_get_irq_reg_offset(kDifRvTimerIntrRegState, irq, &reg_offset)) {
    return kDifBadArg;
  }
  uint32_t intr_state_reg =
      mmio_region_read32(rv_timer->base_addr, (ptrdiff_t)reg_offset);

  *is_pending = bitfield_bit32_read(intr_state_reg, index);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_timer_irq_acknowledge_all(const dif_rv_timer_t *rv_timer,
                                              uint32_t hart_id) {
  if (rv_timer == NULL) {
    return kDifBadArg;
  }

  // Writing to the register clears the corresponding bits (Write-one clear).
  switch (hart_id) {
    case 0:
      mmio_region_write32(rv_timer->base_addr,
                          (ptrdiff_t)RV_TIMER_INTR_STATE0_REG_OFFSET,
                          UINT32_MAX);

      break;
    default:
      return kDifBadArg;
  }

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_timer_irq_acknowledge(const dif_rv_timer_t *rv_timer,
                                          dif_rv_timer_irq_t irq) {
  if (rv_timer == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t index;
  if (!rv_timer_get_irq_bit_index(irq, &index)) {
    return kDifBadArg;
  }

  // Writing to the register clears the corresponding bits (Write-one clear).
  uint32_t intr_state_reg = bitfield_bit32_write(0, index, true);
  uint32_t reg_offset = 0;
  if (!rv_timer_get_irq_reg_offset(kDifRvTimerIntrRegState, irq, &reg_offset)) {
    return kDifBadArg;
  }
  mmio_region_write32(rv_timer->base_addr, (ptrdiff_t)reg_offset,
                      intr_state_reg);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_timer_irq_force(const dif_rv_timer_t *rv_timer,
                                    dif_rv_timer_irq_t irq, const bool val) {
  if (rv_timer == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t index;
  if (!rv_timer_get_irq_bit_index(irq, &index)) {
    return kDifBadArg;
  }

  uint32_t intr_test_reg = bitfield_bit32_write(0, index, val);
  uint32_t reg_offset = 0;
  if (!rv_timer_get_irq_reg_offset(kDifRvTimerIntrRegTest, irq, &reg_offset)) {
    return kDifBadArg;
  }
  mmio_region_write32(rv_timer->base_addr, (ptrdiff_t)reg_offset,
                      intr_test_reg);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_timer_irq_get_enabled(const dif_rv_timer_t *rv_timer,
                                          dif_rv_timer_irq_t irq,
                                          dif_toggle_t *state) {
  if (rv_timer == NULL || state == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t index;
  if (!rv_timer_get_irq_bit_index(irq, &index)) {
    return kDifBadArg;
  }

  uint32_t reg_offset = 0;
  if (!rv_timer_get_irq_reg_offset(kDifRvTimerIntrRegEnable, irq,
                                   &reg_offset)) {
    return kDifBadArg;
  }
  uint32_t intr_enable_reg =
      mmio_region_read32(rv_timer->base_addr, (ptrdiff_t)reg_offset);

  bool is_enabled = bitfield_bit32_read(intr_enable_reg, index);
  *state = is_enabled ? kDifToggleEnabled : kDifToggleDisabled;

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_timer_irq_set_enabled(const dif_rv_timer_t *rv_timer,
                                          dif_rv_timer_irq_t irq,
                                          dif_toggle_t state) {
  if (rv_timer == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t index;
  if (!rv_timer_get_irq_bit_index(irq, &index)) {
    return kDifBadArg;
  }

  uint32_t reg_offset = 0;
  if (!rv_timer_get_irq_reg_offset(kDifRvTimerIntrRegEnable, irq,
                                   &reg_offset)) {
    return kDifBadArg;
  }
  uint32_t intr_enable_reg =
      mmio_region_read32(rv_timer->base_addr, (ptrdiff_t)reg_offset);

  bool enable_bit = (state == kDifToggleEnabled) ? true : false;
  intr_enable_reg = bitfield_bit32_write(intr_enable_reg, index, enable_bit);
  mmio_region_write32(rv_timer->base_addr, (ptrdiff_t)reg_offset,
                      intr_enable_reg);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_timer_irq_disable_all(
    const dif_rv_timer_t *rv_timer, uint32_t hart_id,
    dif_rv_timer_irq_enable_snapshot_t *snapshot) {
  if (rv_timer == NULL) {
    return kDifBadArg;
  }

  // Pass the current interrupt state to the caller, if requested.
  if (snapshot != NULL) {
    switch (hart_id) {
      case 0:
        *snapshot = mmio_region_read32(
            rv_timer->base_addr, (ptrdiff_t)RV_TIMER_INTR_ENABLE0_REG_OFFSET);

        break;
      default:
        return kDifBadArg;
    }
  }

  // Disable all interrupts.
  switch (hart_id) {
    case 0:
      mmio_region_write32(rv_timer->base_addr,
                          (ptrdiff_t)RV_TIMER_INTR_ENABLE0_REG_OFFSET, 0u);

      break;
    default:
      return kDifBadArg;
  }

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_timer_irq_restore_all(
    const dif_rv_timer_t *rv_timer, uint32_t hart_id,
    const dif_rv_timer_irq_enable_snapshot_t *snapshot) {
  if (rv_timer == NULL || snapshot == NULL) {
    return kDifBadArg;
  }

  switch (hart_id) {
    case 0:
      mmio_region_write32(rv_timer->base_addr,
                          (ptrdiff_t)RV_TIMER_INTR_ENABLE0_REG_OFFSET,
                          *snapshot);

      break;
    default:
      return kDifBadArg;
  }

  return kDifOk;
}
