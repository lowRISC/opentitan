// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_rv_timer.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static dif_rv_timer_t timer;

enum {
  kHart = kTopEarlgreyPlicTargetIbex0,
  kComparator = 0,
  kReferenceTimeMillis = 5,
};

OTTF_DEFINE_TEST_CONFIG();

static status_t set_tick(uint32_t tick_hz) {
  dif_rv_timer_tick_params_t tick_params;
  TRY(dif_rv_timer_approximate_tick_params(kClockFreqPeripheralHz, tick_hz,
                                           &tick_params));
  TRY(dif_rv_timer_set_tick_params(&timer, kHart, tick_params));
  return OK_STATUS();
}

static status_t test_tick(uint32_t tick_hz) {
  LOG_INFO("%s: tick_hz = %u", __func__, tick_hz);

  TRY(set_tick(tick_hz));

  uint64_t counter = 0;
  TRY(dif_rv_timer_counter_write(&timer, kHart, counter));
  TRY(dif_rv_timer_counter_read(&timer, kHart, &counter));
  TRY_CHECK(counter == 0, "Failed to write the counter");

  TRY(dif_rv_timer_counter_set_enabled(&timer, kHart, kDifToggleEnabled));
  busy_spin_micros(kReferenceTimeMillis * 1000);
  TRY(dif_rv_timer_counter_set_enabled(&timer, kHart, kDifToggleDisabled));

  TRY(dif_rv_timer_counter_read(&timer, kHart, &counter));
  const uint64_t elapsed_millis = udiv64_slow(counter * 1000, tick_hz, NULL);

  // Verify that `n * T ~= 5 milliseconds` within 3% of tolerance.
  TRY_CHECK((elapsed_millis >= (uint64_t)(kReferenceTimeMillis * 0.97)) &&
                (elapsed_millis <= (uint64_t)(kReferenceTimeMillis * 1.03)),
            "Unexpected elapsed time, expected: %u, got: %u",
            (uint32_t)kReferenceTimeMillis, (uint32_t)elapsed_millis);

  return OK_STATUS();
}

/**
 * Verify that the timer can be configured to generate a system tick.
 *  - Configure the timer to generate a tick of `T` microseconds long.
 *  - Enable the timer.
 *  - Start a busy loop of 5 milliseconds based on the `mcycleh` CSR.
 *  - Read the number of ticks `n`.
 *  - Verify that `n * T ~= 5 milliseconds` within 3% of tolerance.
 *  - Repeat for T in:
 *      [1, 5, 25, 100, 125]
 */
bool test_main(void) {
  CHECK_DIF_OK(dif_rv_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_TIMER_BASE_ADDR), &timer));
  CHECK_DIF_OK(dif_rv_timer_reset(&timer));

  const uint32_t kTickHz[] = {
      1 * 1000 * 1000,  // 1MHz - 1us.
      200 * 1000,       // 200kHz - 5us.
      40 * 1000,        // 40kHz - 25us.
      10 * 1000,        // 10kHz - 100us.
      8 * 1000,         // 8kHz - 125us.
  };

  status_t result = OK_STATUS();
  for (size_t i = 0; i < ARRAYSIZE(kTickHz); ++i) {
    EXECUTE_TEST(result, test_tick, kTickHz[i]);
  }

  return status_ok(result);
}
