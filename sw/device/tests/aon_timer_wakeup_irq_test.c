// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/freestanding/limits.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_rv_timer.h"
#include "sw/device/lib/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/rand_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/FreeRTOSConfig.h"
#include "sw/device/lib/testing/test_framework/ottf.h"
#include "sw/device/lib/testing/test_framework/test_status.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

const test_config_t kTestConfig;

static const uint32_t kPlicTarget = kTopEarlgreyPlicTargetIbex0;
static const uint32_t kTickFreqHz = 1000 * 1000;  // 1Mhz / 1us
static dif_aon_timer_t aon_timer;
static dif_rv_timer_t rv_timer;
static dif_rv_plic_t plic;

static volatile dif_aon_timer_irq_t irq;
static volatile top_earlgrey_plic_peripheral_t peripheral;
static volatile uint64_t time_elapsed;

// TODO:(lowrisc/opentitan#9984): Add timing API to the test framework
/**
 * Initialize the rv timer to count the tick.
 *
 * The `ibex_mcycle_read` function uses the `mcycle` register to count
 * instructions cycles executed and measure time elapsed between two instants,
 * however it stops counting when the `wfi` is called. As this test is based on
 * the `wfi` instruction the best approach then to measure the time elapsed is
 * to use the mtime register, which is basically attached to rv_timer in the
 * opentitan.
 * https://docs.opentitan.org/hw/ip/rv_timer/doc/
 *
 * This is fine due to the test running in a single thread of execution,
 * however, care should be taken in case it changes. OTTF configures the
 * timer in vPortSetupTimerInterrupt, and re-initialising it inside the test
 * could potentially break or cause unexpected behaviour of the test framework.
 */
static_assert(configUSE_PREEMPTION == 0,
              "rv_timer may be initialized already by FreeRtos");

static void tick_init(void) {
  CHECK_DIF_OK(dif_rv_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_TIMER_BASE_ADDR), &rv_timer));

  CHECK_DIF_OK(dif_rv_timer_reset(&rv_timer));

  // Compute and set tick parameters (i.e., step, prescale, etc.).
  dif_rv_timer_tick_params_t tick_params;
  CHECK_DIF_OK(dif_rv_timer_approximate_tick_params(kClockFreqPeripheralHz,
                                                    kTickFreqHz, &tick_params));

  CHECK_DIF_OK(
      dif_rv_timer_set_tick_params(&rv_timer, kPlicTarget, tick_params));

  CHECK_DIF_OK(dif_rv_timer_counter_set_enabled(&rv_timer, kPlicTarget,
                                                kDifToggleEnabled));
}

/**
 * Read the current rv timer count/tick.
 *
 * @return The current rv timer count.
 */
static uint64_t tick_count_get(void) {
  uint64_t tick = 0;
  CHECK_DIF_OK(dif_rv_timer_counter_read(&rv_timer, kPlicTarget, &tick));
  return tick;
}

/**
 * Execute the wake up interrupt test.
 */
static void execute_test(dif_aon_timer_t *aon_timer, uint32_t sleep_time_us) {
  peripheral = kTopEarlgreyPlicPeripheralUnknown;
  irq = kDifAonTimerIrqWdogTimerBark;
  // The wake up time should be `sleepTime_us ±5%`.
  uint32_t variation = sleep_time_us * 5 / 100;
  CHECK(variation > 0);
  uint32_t sleep_range_h = sleep_time_us + variation;
  uint32_t sleep_range_l = sleep_time_us - variation;

  // Setup the timer and wait for the IRQ.
  uint32_t sleep_cycles = (sleep_time_us * kClockFreqAonHz / 1000000);
  LOG_INFO("Setting wakeup interrupt for %u us (%u cycles)", sleep_time_us,
           sleep_cycles);

  aon_timer_testutils_wakeup_config(aon_timer, sleep_cycles);
  // Capture the current tick to measure the time the IRQ will take.
  time_elapsed = tick_count_get();
  do {
    wait_for_interrupt();
  } while (peripheral != kTopEarlgreyPlicPeripheralAonTimerAon &&
           time_elapsed < sleep_range_h);

  CHECK(time_elapsed < sleep_range_h && time_elapsed > sleep_range_l,
        "Timer took %u usec which is not in the range %u usec and %u usec",
        (uint32_t)time_elapsed, sleep_range_l, sleep_range_h);

  CHECK(peripheral == kTopEarlgreyPlicPeripheralAonTimerAon,
        "Interrupt from incorrect peripheral: exp = %d, obs = %d",
        kTopEarlgreyPlicPeripheralAonTimerAon, peripheral);

  CHECK(irq == kDifAonTimerIrqWkupTimerExpired,
        "Interrupt type incorrect: exp = %d, obs = %d",
        kDifAonTimerIrqWkupTimerExpired, irq);
}

/**
 * External interrupt handler.
 */
void ottf_external_isr(void) {
  // Calc the elapsed time since the activation of the IRQ.
  time_elapsed = tick_count_get() - time_elapsed;

  dif_rv_plic_irq_id_t irq_id;
  CHECK_DIF_OK(dif_rv_plic_irq_claim(&plic, kPlicTarget, &irq_id));

  peripheral = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[irq_id];

  if (peripheral == kTopEarlgreyPlicPeripheralAonTimerAon) {
    irq = (dif_aon_timer_irq_t)(
        irq_id -
        (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdAonTimerAonWkupTimerExpired);
    CHECK_DIF_OK(dif_aon_timer_irq_acknowledge(&aon_timer, irq));
  }

  // Complete the IRQ by writing the IRQ source to the Ibex specific CC.
  // register
  CHECK_DIF_OK(dif_rv_plic_irq_complete(&plic, kPlicTarget, irq_id));
}

bool test_main(void) {
  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  // Initialize the rv timer to compute the tick.
  tick_init();

  // Initialize pwrmgr.
  dif_pwrmgr_t pwrmgr;
  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));

  // Initialize aon timer.
  CHECK_DIF_OK(dif_aon_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR), &aon_timer));

  CHECK_DIF_OK(dif_pwrmgr_irq_set_enabled(&pwrmgr, kDifPwrmgrIrqWakeup,
                                          kDifToggleEnabled));

  // Initialize the PLIC.
  mmio_region_t plic_base_addr =
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_plic_init(plic_base_addr, &plic));

  // Enable all the AON interrupts to check if the timer will fire only the
  // correct one.
  rv_plic_testutils_irq_range_enable(
      &plic, kPlicTarget, kTopEarlgreyPlicIrqIdAonTimerAonWkupTimerExpired,
      kTopEarlgreyPlicIrqIdAonTimerAonWdogTimerBark);

  // Executing the test using a randon time between 1 and 15 ms to make sure
  // the aon timer is generating the interrupt after the choosen time and theres
  // no error in the reference time measurement.
  uint32_t sleep_time = rand_testutils_gen32_range(1, 15) * 1000;
  execute_test(&aon_timer, sleep_time);

  return true;
}
