// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_aon_timer.h"

#include <assert.h>
#include <stddef.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/mmio.h"

#include "aon_timer_regs.h"  // Generated.

static_assert(AON_TIMER_INTR_STATE_WKUP_TIMER_EXPIRED_BIT ==
                  AON_TIMER_INTR_TEST_WKUP_TIMER_EXPIRED_BIT,
              "Wake-up IRQ have different indexes in different registers!");
static_assert(AON_TIMER_INTR_STATE_WDOG_TIMER_BARK_BIT ==
                  AON_TIMER_INTR_TEST_WDOG_TIMER_BARK_BIT,
              "Watchdog IRQ have different indexes in different registers!");

const size_t kAonTimerWakeupIrqIndex =
    AON_TIMER_INTR_STATE_WKUP_TIMER_EXPIRED_BIT;

const size_t kAonTimerWatchdogIrqIndex =
    AON_TIMER_INTR_STATE_WDOG_TIMER_BARK_BIT;

static void aon_timer_wakeup_clear_counter(const dif_aon_timer_t *aon) {
  mmio_region_write32(aon->params.base_addr, AON_TIMER_WKUP_COUNT_REG_OFFSET,
                      0);
}

static void aon_timer_wakeup_toggle(const dif_aon_timer_t *aon, bool enable) {
  uint32_t reg =
      mmio_region_read32(aon->params.base_addr, AON_TIMER_WKUP_CTRL_REG_OFFSET);
  reg = bitfield_bit32_write(reg, AON_TIMER_WKUP_CTRL_ENABLE_BIT, enable);
  mmio_region_write32(aon->params.base_addr, AON_TIMER_WKUP_CTRL_REG_OFFSET,
                      reg);
}

static void aon_timer_watchdog_clear_counter(const dif_aon_timer_t *aon) {
  mmio_region_write32(aon->params.base_addr, AON_TIMER_WDOG_COUNT_REG_OFFSET,
                      0);
}

static void aon_timer_watchdog_toggle(const dif_aon_timer_t *aon, bool enable) {
  uint32_t reg =
      mmio_region_read32(aon->params.base_addr, AON_TIMER_WDOG_CTRL_REG_OFFSET);
  reg = bitfield_bit32_write(reg, AON_TIMER_WDOG_CTRL_ENABLE_BIT, enable);
  mmio_region_write32(aon->params.base_addr, AON_TIMER_WDOG_CTRL_REG_OFFSET,
                      reg);
}

static void aon_timer_watchdog_lock(const dif_aon_timer_t *aon) {
  // Clear bit to lock the watchdog configuration register until the next reset.
  // Write one to clear the bit.
  mmio_region_write32(aon->params.base_addr, AON_TIMER_WDOG_REGWEN_REG_OFFSET,
                      0x00000001);
}

static bool aon_timer_watchdog_is_locked(const dif_aon_timer_t *aon) {
  uint32_t reg = mmio_region_read32(aon->params.base_addr,
                                    AON_TIMER_WDOG_REGWEN_REG_OFFSET);

  // Locked when bit is cleared.
  return !bitfield_bit32_read(reg, AON_TIMER_WDOG_REGWEN_REGWEN_BIT);
}

static bool aon_timer_get_irq_index(dif_aon_timer_irq_t irq, uint32_t *index) {
  switch (irq) {
    case kDifAonTimerIrqWakeupThreshold:
      *index = kAonTimerWakeupIrqIndex;
      break;
    case kDifAonTimerIrqWatchdogBarkThreshold:
      *index = kAonTimerWatchdogIrqIndex;
      break;
    default:
      return false;
  }

  return true;
}

dif_aon_timer_result_t dif_aon_timer_init(dif_aon_timer_params_t params,
                                          dif_aon_timer_t *aon) {
  if (aon == NULL) {
    return kDifAonTimerBadArg;
  }

  *aon = (dif_aon_timer_t){.params = params};

  return kDifAonTimerOk;
}

dif_aon_timer_result_t dif_aon_timer_wakeup_start(const dif_aon_timer_t *aon,
                                                  uint32_t threshold,
                                                  uint32_t prescaler) {
  if (aon == NULL || prescaler > AON_TIMER_WKUP_CTRL_PRESCALER_MASK) {
    return kDifAonTimerBadArg;
  }

  // The timer should be stopped first, otherwise it will continue counting up.
  aon_timer_wakeup_toggle(aon, false);
  aon_timer_wakeup_clear_counter(aon);

  mmio_region_write32(aon->params.base_addr, AON_TIMER_WKUP_THOLD_REG_OFFSET,
                      threshold);

  uint32_t reg =
      bitfield_field32_write(0, AON_TIMER_WKUP_CTRL_PRESCALER_FIELD, prescaler);
  reg = bitfield_bit32_write(reg, AON_TIMER_WKUP_CTRL_ENABLE_BIT, true);
  mmio_region_write32(aon->params.base_addr, AON_TIMER_WKUP_CTRL_REG_OFFSET,
                      reg);

  return kDifAonTimerOk;
}

dif_aon_timer_result_t dif_aon_timer_wakeup_stop(const dif_aon_timer_t *aon) {
  if (aon == NULL) {
    return kDifAonTimerBadArg;
  }

  aon_timer_wakeup_toggle(aon, false);

  return kDifAonTimerOk;
}

dif_aon_timer_result_t dif_aon_timer_wakeup_restart(
    const dif_aon_timer_t *aon) {
  if (aon == NULL) {
    return kDifAonTimerBadArg;
  }

  aon_timer_wakeup_clear_counter(aon);
  aon_timer_wakeup_toggle(aon, true);

  return kDifAonTimerOk;
}

dif_aon_timer_result_t dif_aon_timer_wakeup_get_count(
    const dif_aon_timer_t *aon, uint32_t *count) {
  if (aon == NULL || count == NULL) {
    return kDifAonTimerBadArg;
  }

  *count = mmio_region_read32(aon->params.base_addr,
                              AON_TIMER_WKUP_COUNT_REG_OFFSET);

  return kDifAonTimerOk;
}

dif_aon_timer_watchdog_result_t dif_aon_timer_watchdog_start(
    const dif_aon_timer_t *aon, uint32_t bark_threshold,
    uint32_t bite_threshold, bool pause_in_sleep, bool lock) {
  if (aon == NULL) {
    return kDifAonTimerWatchdogBadArg;
  }

  if (aon_timer_watchdog_is_locked(aon)) {
    return kDifAonTimerWatchdogLocked;
  }

  // The timer should be stopped first, otherwise it will continue counting up.
  aon_timer_watchdog_toggle(aon, false);
  aon_timer_watchdog_clear_counter(aon);

  mmio_region_write32(aon->params.base_addr,
                      AON_TIMER_WDOG_BARK_THOLD_REG_OFFSET, bark_threshold);
  mmio_region_write32(aon->params.base_addr,
                      AON_TIMER_WDOG_BITE_THOLD_REG_OFFSET, bite_threshold);

  uint32_t reg = bitfield_bit32_write(0, AON_TIMER_WDOG_CTRL_ENABLE_BIT, true);
  if (pause_in_sleep) {
    reg =
        bitfield_bit32_write(reg, AON_TIMER_WDOG_CTRL_PAUSE_IN_SLEEP_BIT, true);
  }
  mmio_region_write32(aon->params.base_addr, AON_TIMER_WDOG_CTRL_REG_OFFSET,
                      reg);

  // Watchdog control register should only be locked after the last
  // control register access.
  if (lock) {
    aon_timer_watchdog_lock(aon);
  }

  return kDifAonTimerWatchdogOk;
}

dif_aon_timer_watchdog_result_t dif_aon_timer_watchdog_stop(
    const dif_aon_timer_t *aon) {
  if (aon == NULL) {
    return kDifAonTimerWatchdogBadArg;
  }

  if (aon_timer_watchdog_is_locked(aon)) {
    return kDifAonTimerWatchdogLocked;
  }

  aon_timer_watchdog_toggle(aon, false);

  return kDifAonTimerWatchdogOk;
}

dif_aon_timer_watchdog_result_t dif_aon_timer_watchdog_restart(
    const dif_aon_timer_t *aon) {
  if (aon == NULL) {
    return kDifAonTimerWatchdogBadArg;
  }

  if (aon_timer_watchdog_is_locked(aon)) {
    return kDifAonTimerWatchdogLocked;
  }

  aon_timer_watchdog_clear_counter(aon);
  aon_timer_watchdog_toggle(aon, true);

  return kDifAonTimerWatchdogOk;
}

dif_aon_timer_result_t dif_aon_timer_watchdog_get_count(
    const dif_aon_timer_t *aon, uint32_t *count) {
  if (aon == NULL || count == NULL) {
    return kDifAonTimerBadArg;
  }

  *count = mmio_region_read32(aon->params.base_addr,
                              AON_TIMER_WDOG_COUNT_REG_OFFSET);

  return kDifAonTimerOk;
}

dif_aon_timer_result_t dif_aon_timer_watchdog_pet(const dif_aon_timer_t *aon) {
  if (aon == NULL) {
    return kDifAonTimerBadArg;
  }

  aon_timer_watchdog_clear_counter(aon);

  return kDifAonTimerOk;
}

dif_aon_timer_watchdog_result_t dif_aon_timer_watchdog_lock(
    const dif_aon_timer_t *aon) {
  if (aon == NULL) {
    return kDifAonTimerWatchdogBadArg;
  }

  aon_timer_watchdog_lock(aon);

  return kDifAonTimerWatchdogOk;
}

dif_aon_timer_result_t dif_aon_timer_watchdog_is_locked(
    const dif_aon_timer_t *aon, bool *is_locked) {
  if (aon == NULL || is_locked == NULL) {
    return kDifAonTimerBadArg;
  }

  *is_locked = aon_timer_watchdog_is_locked(aon);

  return kDifAonTimerOk;
}

dif_aon_timer_result_t dif_aon_timer_irq_is_pending(const dif_aon_timer_t *aon,
                                                    dif_aon_timer_irq_t irq,
                                                    bool *is_pending) {
  if (aon == NULL || is_pending == NULL) {
    return kDifAonTimerBadArg;
  }

  uint32_t index = 0;
  if (!aon_timer_get_irq_index(irq, &index)) {
    return kDifAonTimerError;
  }

  uint32_t reg = mmio_region_read32(aon->params.base_addr,
                                    AON_TIMER_INTR_STATE_REG_OFFSET);
  *is_pending = bitfield_bit32_read(reg, index);

  return kDifAonTimerOk;
}

dif_aon_timer_result_t dif_aon_timer_irq_acknowledge(const dif_aon_timer_t *aon,
                                                     dif_aon_timer_irq_t irq) {
  if (aon == NULL) {
    return kDifAonTimerBadArg;
  }

  uint32_t index = 0;
  if (!aon_timer_get_irq_index(irq, &index)) {
    return kDifAonTimerError;
  }

  // Write one to clear.
  uint32_t reg = bitfield_bit32_write(0, index, true);
  mmio_region_write32(aon->params.base_addr, AON_TIMER_INTR_STATE_REG_OFFSET,
                      reg);

  return kDifAonTimerOk;
}

dif_aon_timer_result_t dif_aon_timer_irq_force(const dif_aon_timer_t *aon,
                                               dif_aon_timer_irq_t irq) {
  if (aon == NULL) {
    return kDifAonTimerBadArg;
  }

  uint32_t index = 0;
  if (!aon_timer_get_irq_index(irq, &index)) {
    return kDifAonTimerError;
  }

  // Write only register.
  uint32_t reg = bitfield_bit32_write(0, index, true);
  mmio_region_write32(aon->params.base_addr, AON_TIMER_INTR_TEST_REG_OFFSET,
                      reg);

  return kDifAonTimerOk;
}
