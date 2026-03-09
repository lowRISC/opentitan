// Copyright lowRISC contributors (OpenTitan project).
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
  kWrapTimeMillis = 5,
};

OTTF_DEFINE_TEST_CONFIG();

static status_t set_tick(uint32_t tick_hz) {
  dif_rv_timer_tick_params_t tick_params;
  TRY(dif_rv_timer_approximate_tick_params(kClockFreqPeripheralHz, tick_hz,
                                           &tick_params));
  TRY(dif_rv_timer_set_tick_params(&timer, kHart, tick_params));
  return OK_STATUS();
}

static status_t test_tick(uint32_t tick_hz, uint32_t tick_low_bound,
                          uint32_t tick_high_bound) {
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

  // Assuming the measured ticks fit in 32 bits simplifies things. That should
  // always be true for the tick frequencies and reference time used in this
  // test (a maximum of ~5000 ticks at the time of writing).
  TRY_CHECK((uint32_t)counter == counter,
            "Measured ticks value does not fit in 32 bits");

  LOG_INFO("Elapsed ticks: %u. Bounds: %u--%u", (uint32_t)counter,
           tick_low_bound, tick_high_bound);

  // Verify that `n * T ~= 5 milliseconds` within 3% of tolerance.
  TRY_CHECK((counter >= tick_low_bound) && (counter <= tick_high_bound),
            "Unexpected elapsed time, expected: %u--%u, got: 0x%u ticks",
            tick_low_bound, tick_high_bound, (uint32_t)counter);

  return OK_STATUS();
}

static status_t test_wrap(uint32_t tick_hz) {
  LOG_INFO("%s: tick_hz = %u", __func__, tick_hz);

  TRY(dif_rv_timer_irq_set_enabled(
      &timer, kDifRvTimerIrqTimerExpiredHart0Timer0, kDifToggleEnabled));

  TRY(set_tick(tick_hz));

  uint64_t start_counter = UINT64_MAX - (kWrapTimeMillis * tick_hz) / 1000;
  TRY(dif_rv_timer_counter_write(&timer, kHart, start_counter));
  TRY(dif_rv_timer_arm(&timer, kHart, 0, UINT64_MAX));

  TRY(dif_rv_timer_counter_set_enabled(&timer, kHart, kDifToggleEnabled));
  busy_spin_micros(kWrapTimeMillis * 1000 * 2);
  TRY(dif_rv_timer_counter_set_enabled(&timer, kHart, kDifToggleDisabled));

  uint64_t counter = UINT64_MAX;
  TRY(dif_rv_timer_counter_read(&timer, kHart, &counter));
  // Verify that the counter wrapped.
  TRY_CHECK(counter < start_counter,
            "Unexpected elapsed time, expected: %08x%08x, got: %08x%08x",
            (uint32_t)(start_counter >> 32), (uint32_t)start_counter,
            (uint32_t)(counter >> 32), (uint32_t)counter);

  bool irq_pending = false;
  TRY(dif_rv_timer_irq_is_pending(&timer, kDifRvTimerIrqTimerExpiredHart0Timer0,
                                  &irq_pending));
  TRY_CHECK(irq_pending, "Expected timer IRQ");
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

// Macros to calculate the 97%--103% tick tolerance values
#define LOW_TICK_BOUND(x) ((x) / ((1000 + 30) / kReferenceTimeMillis))
#define HIGH_TICK_BOUND(x) ((x) / ((1000 - 30) / kReferenceTimeMillis))
#define VALUE_AND_BOUNDS(x) (x), LOW_TICK_BOUND(x), HIGH_TICK_BOUND(x)

  const uint32_t kTickHz[] = {
      VALUE_AND_BOUNDS(1 * 1000 * 1000),  // 1MHz - 1us.
      VALUE_AND_BOUNDS(200 * 1000),       // 200kHz - 5us.
      VALUE_AND_BOUNDS(40 * 1000),        // 40kHz - 25us.
      VALUE_AND_BOUNDS(10 * 1000),        // 10kHz - 100us.
      VALUE_AND_BOUNDS(8 * 1000),         // 8kHz - 125us.
  };

  status_t result = OK_STATUS();
  for (size_t i = 0; i < ARRAYSIZE(kTickHz); i += 3) {
    EXECUTE_TEST(result, test_tick, kTickHz[i], kTickHz[i + 1], kTickHz[i + 2]);
  }

  EXECUTE_TEST(result, test_wrap, 10000);

  return status_ok(result);
}
