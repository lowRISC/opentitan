// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/aon_timer_testutils.h"

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/testing/test_framework/check.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

status_t aon_timer_testutils_get_aon_cycles_from_us(uint64_t microseconds,
                                                    uint32_t *cycles) {
  uint64_t cycles_ = udiv64_slow(microseconds * kClockFreqAonHz, 1000000,
                                 /*rem_out=*/NULL);
  TRY_CHECK(cycles_ <= UINT32_MAX,
            "The value 0x%08x%08x can't fit into the 32 bits timer counter.",
            (cycles_ >> 32), (uint32_t)cycles_);
  *cycles = (uint32_t)cycles_;
  return OK_STATUS();
}

status_t aon_timer_testutils_get_us_from_aon_cycles(uint64_t cycles,
                                                    uint32_t *us) {
  uint64_t uss = udiv64_slow(cycles * 1000000, kClockFreqAonHz,
                             /*rem_out=*/NULL);
  TRY_CHECK(uss <= UINT32_MAX,
            "The value 0x%08x%08x can't fit into the 32 bits timer counter.",
            (uss >> 32), (uint32_t)uss);
  *us = (uint32_t)uss;
  return OK_STATUS();
}

status_t aon_timer_testutils_wakeup_config(const dif_aon_timer_t *aon_timer,
                                           uint32_t cycles) {
  // Make sure that wake-up timer is stopped.
  TRY(dif_aon_timer_wakeup_stop(aon_timer));

  // Make sure the wake-up IRQ is cleared to avoid false positive.
  TRY(dif_aon_timer_irq_acknowledge(aon_timer,
                                    kDifAonTimerIrqWkupTimerExpired));

  bool is_pending = true;
  TRY(dif_aon_timer_irq_is_pending(aon_timer, kDifAonTimerIrqWkupTimerExpired,
                                   &is_pending));
  TRY_CHECK(!is_pending);

  // Set prescaler to zero.
  TRY(dif_aon_timer_wakeup_start(aon_timer, cycles, 0));
  return OK_STATUS();
}

status_t aon_timer_testutils_watchdog_config(const dif_aon_timer_t *aon_timer,
                                             uint32_t bark_cycles,
                                             uint32_t bite_cycles,
                                             bool pause_in_sleep) {
  // Make sure that watchdog timer is stopped.
  TRY(dif_aon_timer_watchdog_stop(aon_timer));

  // Make sure the watchdog IRQ is cleared to avoid false positive.
  TRY(dif_aon_timer_irq_acknowledge(aon_timer, kDifAonTimerIrqWdogTimerBark));
  bool is_pending = true;
  TRY(dif_aon_timer_irq_is_pending(aon_timer, kDifAonTimerIrqWdogTimerBark,
                                   &is_pending));
  TRY_CHECK(!is_pending);
  TRY(dif_aon_timer_watchdog_start(aon_timer, bark_cycles, bite_cycles,
                                   pause_in_sleep, false));
  return OK_STATUS();
}

status_t aon_timer_testutils_shutdown(const dif_aon_timer_t *aon_timer) {
  TRY(dif_aon_timer_wakeup_stop(aon_timer));
  TRY(dif_aon_timer_watchdog_stop(aon_timer));
  TRY(dif_aon_timer_clear_wakeup_cause(aon_timer));
  TRY(dif_aon_timer_irq_acknowledge_all(aon_timer));
  // Read and verify both timers are actually disabled. This ensures the
  // synchronization from the core clock to the AON clock domain completed.
  bool enabled;
  TRY(dif_aon_timer_wakeup_is_enabled(aon_timer, &enabled));
  TRY_CHECK(enabled == false);
  TRY(dif_aon_timer_watchdog_is_enabled(aon_timer, &enabled));
  TRY_CHECK(enabled == false);
  return OK_STATUS();
}
