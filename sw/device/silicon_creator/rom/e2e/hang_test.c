// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>

#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  dif_aon_timer_t aon_timer;
  CHECK_DIF_OK(dif_aon_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR), &aon_timer));
  /* Pet the watchdog to have make sure that we start from a known value */
  CHECK_DIF_OK(dif_aon_timer_watchdog_pet(&aon_timer));
  ibex_timeout_t timeout = ibex_timeout_init(HANG_SECS * 1000000);
  while (!ibex_timeout_check(&timeout)) {
  }
  /* Get the watchdog count value */
  uint32_t count;
  CHECK_DIF_OK(dif_aon_timer_watchdog_get_count(&aon_timer, &count));
  LOG_INFO("Returning after %d seconds", HANG_SECS);
  LOG_INFO("Watchdog count: %d", count);
  return true;
}
