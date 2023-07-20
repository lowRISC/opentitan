// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_aon_timer.h"

#include <assert.h>
#include <stddef.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"

#include "aon_timer_regs.h"  // Generated.

static_assert(AON_TIMER_INTR_STATE_WKUP_TIMER_EXPIRED_BIT ==
                  AON_TIMER_INTR_TEST_WKUP_TIMER_EXPIRED_BIT,
              "Wake-up IRQ have different indexes in different registers!");
static_assert(AON_TIMER_INTR_STATE_WDOG_TIMER_BARK_BIT ==
                  AON_TIMER_INTR_TEST_WDOG_TIMER_BARK_BIT,
              "Watchdog IRQ have different indexes in different registers!");

static void aon_timer_wakeup_clear_counter(const dif_aon_timer_t *aon) {
  mmio_region_write32(aon->base_addr, AON_TIMER_WKUP_COUNT_REG_OFFSET, 0);
}

static void aon_timer_wakeup_toggle(const dif_aon_timer_t *aon, bool enable) {
  uint32_t reg =
      mmio_region_read32(aon->base_addr, AON_TIMER_WKUP_CTRL_REG_OFFSET);
  reg = bitfield_bit32_write(reg, AON_TIMER_WKUP_CTRL_ENABLE_BIT, enable);
  mmio_region_write32(aon->base_addr, AON_TIMER_WKUP_CTRL_REG_OFFSET, reg);
}

static void aon_timer_watchdog_clear_counter(const dif_aon_timer_t *aon) {
  mmio_region_write32(aon->base_addr, AON_TIMER_WDOG_COUNT_REG_OFFSET, 0);
}

static void aon_timer_watchdog_toggle(const dif_aon_timer_t *aon, bool enable) {
  uint32_t reg =
      mmio_region_read32(aon->base_addr, AON_TIMER_WDOG_CTRL_REG_OFFSET);
  reg = bitfield_bit32_write(reg, AON_TIMER_WDOG_CTRL_ENABLE_BIT, enable);
  mmio_region_write32(aon->base_addr, AON_TIMER_WDOG_CTRL_REG_OFFSET, reg);
}

static void aon_timer_watchdog_lock(const dif_aon_timer_t *aon) {
  // Clear bit to lock the watchdog configuration register until the next reset.
  // Write one to clear the bit.
  mmio_region_write32(aon->base_addr, AON_TIMER_WDOG_REGWEN_REG_OFFSET,
                      0x00000001);
}

static bool aon_timer_watchdog_is_locked(const dif_aon_timer_t *aon) {
  uint32_t reg =
      mmio_region_read32(aon->base_addr, AON_TIMER_WDOG_REGWEN_REG_OFFSET);

  // Locked when bit is cleared.
  return !bitfield_bit32_read(reg, AON_TIMER_WDOG_REGWEN_REGWEN_BIT);
}

dif_result_t dif_aon_timer_wakeup_start(const dif_aon_timer_t *aon,
                                        uint32_t threshold,
                                        uint32_t prescaler) {
  if (aon == NULL || prescaler > AON_TIMER_WKUP_CTRL_PRESCALER_MASK) {
    return kDifBadArg;
  }

  // The timer should be stopped first, otherwise it will continue counting up.
  aon_timer_wakeup_toggle(aon, false);
  aon_timer_wakeup_clear_counter(aon);

  // As AON_TIMER spends one more cycle to create the interrupt, subtract
  // cycles by 1 here.
  mmio_region_write32(aon->base_addr, AON_TIMER_WKUP_THOLD_REG_OFFSET,
                      threshold - 1);

  uint32_t reg =
      bitfield_field32_write(0, AON_TIMER_WKUP_CTRL_PRESCALER_FIELD, prescaler);
  reg = bitfield_bit32_write(reg, AON_TIMER_WKUP_CTRL_ENABLE_BIT, true);
  mmio_region_write32(aon->base_addr, AON_TIMER_WKUP_CTRL_REG_OFFSET, reg);

  return kDifOk;
}

dif_result_t dif_aon_timer_wakeup_stop(const dif_aon_timer_t *aon) {
  if (aon == NULL) {
    return kDifBadArg;
  }

  aon_timer_wakeup_toggle(aon, false);

  return kDifOk;
}

dif_result_t dif_aon_timer_wakeup_restart(const dif_aon_timer_t *aon) {
  if (aon == NULL) {
    return kDifBadArg;
  }

  aon_timer_wakeup_clear_counter(aon);
  aon_timer_wakeup_toggle(aon, true);

  return kDifOk;
}

dif_result_t dif_aon_timer_wakeup_is_enabled(const dif_aon_timer_t *aon,
                                             bool *is_enabled) {
  if (aon == NULL || is_enabled == NULL) {
    return kDifBadArg;
  }

  uint32_t reg =
      mmio_region_read32(aon->base_addr, AON_TIMER_WKUP_CTRL_REG_OFFSET);

  *is_enabled = bitfield_bit32_read(reg, AON_TIMER_WKUP_CTRL_ENABLE_BIT);

  return kDifOk;
}

dif_result_t dif_aon_timer_clear_wakeup_cause(const dif_aon_timer_t *aon) {
  if (aon == NULL) {
    return kDifBadArg;
  }
  mmio_region_write32(aon->base_addr, AON_TIMER_WKUP_CAUSE_REG_OFFSET, 0);
  return kDifOk;
}

dif_result_t dif_aon_timer_wakeup_get_count(const dif_aon_timer_t *aon,
                                            uint32_t *count) {
  if (aon == NULL || count == NULL) {
    return kDifBadArg;
  }

  *count = mmio_region_read32(aon->base_addr, AON_TIMER_WKUP_COUNT_REG_OFFSET);

  return kDifOk;
}

dif_result_t dif_aon_timer_watchdog_start(const dif_aon_timer_t *aon,
                                          uint32_t bark_threshold,
                                          uint32_t bite_threshold,
                                          bool pause_in_sleep, bool lock) {
  if (aon == NULL) {
    return kDifBadArg;
  }

  if (aon_timer_watchdog_is_locked(aon)) {
    return kDifLocked;
  }

  // The timer should be stopped first, otherwise it will continue counting up.
  aon_timer_watchdog_toggle(aon, false);
  aon_timer_watchdog_clear_counter(aon);

  // As AON_TIMER spends one more cycle to create the interrupt, subtract
  // cycles by 1 here.
  mmio_region_write32(aon->base_addr, AON_TIMER_WDOG_BARK_THOLD_REG_OFFSET,
                      bark_threshold - 1);
  mmio_region_write32(aon->base_addr, AON_TIMER_WDOG_BITE_THOLD_REG_OFFSET,
                      bite_threshold - 1);

  uint32_t reg = bitfield_bit32_write(0, AON_TIMER_WDOG_CTRL_ENABLE_BIT, true);
  if (pause_in_sleep) {
    reg =
        bitfield_bit32_write(reg, AON_TIMER_WDOG_CTRL_PAUSE_IN_SLEEP_BIT, true);
  }
  mmio_region_write32(aon->base_addr, AON_TIMER_WDOG_CTRL_REG_OFFSET, reg);

  // Watchdog control register should only be locked after the last
  // control register access.
  if (lock) {
    aon_timer_watchdog_lock(aon);
  }

  return kDifOk;
}

dif_result_t dif_aon_timer_watchdog_stop(const dif_aon_timer_t *aon) {
  if (aon == NULL) {
    return kDifBadArg;
  }

  if (aon_timer_watchdog_is_locked(aon)) {
    return kDifLocked;
  }

  aon_timer_watchdog_toggle(aon, false);

  return kDifOk;
}

dif_result_t dif_aon_timer_watchdog_restart(const dif_aon_timer_t *aon) {
  if (aon == NULL) {
    return kDifBadArg;
  }

  if (aon_timer_watchdog_is_locked(aon)) {
    return kDifLocked;
  }

  aon_timer_watchdog_clear_counter(aon);
  aon_timer_watchdog_toggle(aon, true);

  return kDifOk;
}

dif_result_t dif_aon_timer_watchdog_is_enabled(const dif_aon_timer_t *aon,
                                               bool *is_enabled) {
  if (aon == NULL || is_enabled == NULL) {
    return kDifBadArg;
  }

  uint32_t reg =
      mmio_region_read32(aon->base_addr, AON_TIMER_WDOG_CTRL_REG_OFFSET);

  *is_enabled = bitfield_bit32_read(reg, AON_TIMER_WDOG_CTRL_ENABLE_BIT);

  return kDifOk;
}

dif_result_t dif_aon_timer_watchdog_get_count(const dif_aon_timer_t *aon,
                                              uint32_t *count) {
  if (aon == NULL || count == NULL) {
    return kDifBadArg;
  }

  *count = mmio_region_read32(aon->base_addr, AON_TIMER_WDOG_COUNT_REG_OFFSET);

  return kDifOk;
}

dif_result_t dif_aon_timer_watchdog_pet(const dif_aon_timer_t *aon) {
  if (aon == NULL) {
    return kDifBadArg;
  }

  aon_timer_watchdog_clear_counter(aon);

  return kDifOk;
}

dif_result_t dif_aon_timer_watchdog_lock(const dif_aon_timer_t *aon) {
  if (aon == NULL) {
    return kDifBadArg;
  }

  aon_timer_watchdog_lock(aon);

  return kDifOk;
}

dif_result_t dif_aon_timer_watchdog_is_locked(const dif_aon_timer_t *aon,
                                              bool *is_locked) {
  if (aon == NULL || is_locked == NULL) {
    return kDifBadArg;
  }

  *is_locked = aon_timer_watchdog_is_locked(aon);

  return kDifOk;
}
