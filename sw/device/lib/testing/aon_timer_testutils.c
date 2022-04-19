// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/aon_timer_testutils.h"

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/testing/test_framework/check.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

uint32_t aon_timer_testutils_get_aon_cycles_from_us(uint64_t microseconds) {
  uint64_t cycles = udiv64_slow(microseconds * kClockFreqAonHz, 1000000, NULL);
  CHECK(cycles < UINT32_MAX,
        "The value 0x%08x%08x can't fit into the 32 bits timer counter.",
        (cycles >> 32), (uint32_t)cycles);
  return (uint32_t)cycles;
}

void aon_timer_testutils_wakeup_config(const dif_aon_timer_t *aon_timer,
                                       uint32_t cycles) {
  // Make sure that wake-up timer is stopped.
  CHECK_DIF_OK(dif_aon_timer_wakeup_stop(aon_timer));

  // Make sure the wake-up IRQ is cleared to avoid false positive.
  CHECK_DIF_OK(dif_aon_timer_irq_acknowledge(aon_timer,
                                             kDifAonTimerIrqWkupTimerExpired));

  bool is_pending = true;
  CHECK_DIF_OK(dif_aon_timer_irq_is_pending(
      aon_timer, kDifAonTimerIrqWkupTimerExpired, &is_pending));
  CHECK(!is_pending);

  // Set prescaler to zero.
  CHECK_DIF_OK(dif_aon_timer_wakeup_start(aon_timer, cycles, 0));
}

void aon_timer_testutils_watchdog_config(const dif_aon_timer_t *aon_timer,
                                         uint32_t bark_cycles,
                                         uint32_t bite_cycles,
                                         bool pause_in_sleep) {
  // Make sure that watchdog timer is stopped.
  CHECK_DIF_OK(dif_aon_timer_watchdog_stop(aon_timer));

  // Make sure the watchdog IRQ is cleared to avoid false positive.
  CHECK_DIF_OK(
      dif_aon_timer_irq_acknowledge(aon_timer, kDifAonTimerIrqWdogTimerBark));
  bool is_pending = true;
  CHECK_DIF_OK(dif_aon_timer_irq_is_pending(
      aon_timer, kDifAonTimerIrqWdogTimerBark, &is_pending));
  CHECK(!is_pending);
  CHECK_DIF_OK(dif_aon_timer_watchdog_start(aon_timer, bark_cycles, bite_cycles,
                                            pause_in_sleep, false));
}
