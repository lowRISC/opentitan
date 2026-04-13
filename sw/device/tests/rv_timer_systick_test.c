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
  TRY_CHECK(counter <= UINT32_MAX,
            "uint32_t overflow, refactor this code to use uint64_t instead");
  // To find total ticks, we need (ms / 1000) * Hz.
  // We use (ms * Hz) vs (counter * 1000) to keep all operations as
  // multiplications.
  const uint32_t ticks = (uint32_t)counter * 1000;
  const uint32_t reference_ticks = kReferenceTimeMillis * tick_hz;

  // Verify that `n * T ~= 5 milliseconds` within 3% of tolerance.
  // `ticks * 100 == ref * 97` is equivalent to `ticks == ref * 0.97`)
  TRY_CHECK((ticks * 100 >= reference_ticks * 97) &&
                (ticks * 100 <= reference_ticks * 103),
            "Unexpected elapsed time, expected: %u ticks +-3%%, got: %u ticks",
            reference_ticks, ticks);

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

  EXECUTE_TEST(result, test_wrap, 10000);

  return status_ok(result);
}
