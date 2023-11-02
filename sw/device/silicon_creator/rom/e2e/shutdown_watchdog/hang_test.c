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

void print_progress(const char *prefix, dif_aon_timer_t *aon_timer,
                    ibex_timeout_t *timeout) {
  uint32_t count;
  CHECK_DIF_OK(dif_aon_timer_watchdog_get_count(aon_timer, &count));
  uint64_t elapsed = ibex_timeout_elapsed(timeout);
  elapsed = udiv64_slow(elapsed, 1000, NULL);
  LOG_INFO("%s: after %d ms, watchdog count=%d", prefix, (uint32_t)elapsed,
           count);
}

bool test_main(void) {
  dif_aon_timer_t aon_timer;
  CHECK_DIF_OK(dif_aon_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR), &aon_timer));
  /* Pet the watchdog to have make sure that we start from a known value */
  CHECK_DIF_OK(dif_aon_timer_watchdog_pet(&aon_timer));
  ibex_timeout_t timeout = ibex_timeout_init(HANG_SECS * 1000000);
  while (!ibex_timeout_check(&timeout)) {
    // Print a status message every 100ms.
    ibex_timeout_t inter_tmo = ibex_timeout_init(100000);
    while (!ibex_timeout_check(&inter_tmo)) {
    }
    print_progress("Status", &aon_timer, &timeout);
  }
  // Print final status.
  print_progress("Wait done", &aon_timer, &timeout);
  return true;
}
