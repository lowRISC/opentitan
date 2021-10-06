// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/aon_timer_testutils.h"

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/testing/check.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

void aon_timer_testutils_wakeup_config(dif_aon_timer_t *aon_timer,
                                       uint32_t cycles) {
  // Make sure that wake-up timer is stopped.
  CHECK_DIF_OK(dif_aon_timer_wakeup_stop(aon_timer));

  // Make sure the wake-up IRQ is cleared to avoid false positive.
  CHECK_DIF_OK(dif_aon_timer_irq_acknowledge(aon_timer,
                                             kDifAonTimerIrqWkupTimerExpired));

  bool is_pending;
  CHECK_DIF_OK(dif_aon_timer_irq_is_pending(
      aon_timer, kDifAonTimerIrqWkupTimerExpired, &is_pending));
  CHECK(!is_pending);

  CHECK_DIF_OK(dif_aon_timer_wakeup_start(aon_timer, cycles, 0));
}
