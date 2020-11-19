// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_rv_timer.h"

#include "sw/device/lib/handler.h"
#include "sw/device/lib/irq.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_main.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static dif_rv_timer_t timer;

// Flag for checking whether the interrupt handler was called. When the handler
// is entered, this value *must* be set to false, to catch false positives.
//
// This variable is volatile, since it may suddenly change from the compiler's
// perspective (e.g., due to an interrupt firing).
static volatile bool irq_fired = true;

// NOTE: PLIC targets need not line up with hart ids; in the future, we should
// generate hart ID constants elsewhere.
static const uint32_t kHart = (uint32_t)kTopEarlgreyPlicTargetIbex0;
static const uint32_t kComparator = 0;

static const uint64_t kTickFreqHz = 1000 * 1000;  // 1 MHz.

static void test_handler(void) {
  CHECK(!irq_fired, "Entered IRQ handler, but `irq_fired` was not false!");

  bool irq_flag;
  CHECK(dif_rv_timer_irq_get(&timer, kHart, kComparator, &irq_flag) ==
        kDifRvTimerOk);
  CHECK(irq_flag, "Entered IRQ handler but the expected IRQ flag wasn't set!");

  CHECK(dif_rv_timer_counter_set_enabled(&timer, kHart, kDifRvTimerDisabled) ==
        kDifRvTimerOk);
  CHECK(dif_rv_timer_irq_clear(&timer, kHart, kComparator) == kDifRvTimerOk);

  irq_fired = true;
}

// Register our own IRQ handler by overriding a weak symbol in `handler.h`.
void handler_irq_timer(void) {
  LOG_INFO("Entering handler_irq_timer()");
  test_handler();
  LOG_INFO("Exiting handler_irq_timer()");
}

const test_config_t kTestConfig;

bool test_main(void) {
  irq_global_ctrl(true);
  irq_timer_ctrl(true);

  mmio_region_t timer_reg =
      mmio_region_from_addr(TOP_EARLGREY_RV_TIMER_BASE_ADDR);
  CHECK(dif_rv_timer_init(
            timer_reg,
            (dif_rv_timer_config_t){.hart_count = 1, .comparator_count = 1},
            &timer) == kDifRvTimerOk);

  dif_rv_timer_tick_params_t tick_params;
  CHECK(dif_rv_timer_approximate_tick_params(kClockFreqPeripheralHz,
                                             kTickFreqHz, &tick_params) ==
        kDifRvTimerApproximateTickParamsOk);
  CHECK(dif_rv_timer_set_tick_params(&timer, kHart, tick_params) ==
        kDifRvTimerOk);
  CHECK(dif_rv_timer_irq_enable(&timer, kHart, kComparator,
                                kDifRvTimerEnabled) == kDifRvTimerOk);

  uint64_t current_time;
  // Logs over UART incur a large runtime overhead. To accommodate that, the
  // timer deadline needs to be large as well. In DV simulations, logs are not
  // sent over UART, so we can reduce the runtime / sim time with a much shorter
  // deadline (30 ms vs 100 us).
  uint64_t kDeadline =
      (kDeviceType == kDeviceSimDV) ? 100 /* 100 us */ : 30000 /* 30 ms */;
  CHECK(dif_rv_timer_counter_read(&timer, kHart, &current_time) ==
        kDifRvTimerOk);
  LOG_INFO("Current time: %d; timer theshold: %d", (uint32_t)current_time,
           (uint32_t)(current_time + kDeadline));
  CHECK(dif_rv_timer_arm(&timer, kHart, kComparator,
                         current_time + kDeadline) == kDifRvTimerOk);

  irq_fired = false;
  CHECK(dif_rv_timer_counter_set_enabled(&timer, kHart, kDifRvTimerEnabled) ==
        kDifRvTimerOk);

  LOG_INFO("Waiting...");
  while (!irq_fired) {
    wait_for_interrupt();
  }

  return true;
}
