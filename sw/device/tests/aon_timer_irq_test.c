// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <limits.h>
#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_rv_timer.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/rand_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/FreeRTOSConfig.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

static const uint32_t kPlicTarget = kTopEarlgreyPlicTargetIbex0;
static const uint32_t kTickFreqHz = 1000 * 1000;  // 1Mhz / 1us
static dif_rv_core_ibex_t rv_core_ibex;
static dif_aon_timer_t aon_timer;
static dif_rv_timer_t rv_timer;
static dif_rv_plic_t plic;

static volatile dif_aon_timer_irq_t irq;
static volatile top_earlgrey_plic_peripheral_t peripheral;
static volatile uint64_t irq_tick;

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
 * Execute the aon timer interrupt test.
 */
static void execute_test(dif_aon_timer_t *aon_timer, uint64_t irq_time_us,
                         dif_aon_timer_irq_t expected_irq) {
  // The interrupt time should be `irq_time_us ±5%`.
  uint64_t variation = udiv64_slow(irq_time_us * 5, 100, NULL);
  CHECK(variation > 0);
  uint64_t sleep_range_h = irq_time_us + variation;
  uint64_t sleep_range_l = irq_time_us - variation;

  // Add 1500 cpu cycles of overhead to cover irq handling.
  sleep_range_h += udiv64_slow(1500 * 1000000, kClockFreqCpuHz, NULL);

  uint32_t count_cycles = 0;
  CHECK_STATUS_OK(
      aon_timer_testutils_get_aon_cycles_from_us(irq_time_us, &count_cycles));
  LOG_INFO("Setting interrupt for %u us (%u cycles)", (uint32_t)irq_time_us,
           count_cycles);

  // Set the default value to a different value than expected.
  peripheral = kTopEarlgreyPlicPeripheralUnknown;
  irq = kDifAonTimerIrqWdogTimerBark;
  if (expected_irq == kDifAonTimerIrqWkupTimerExpired) {
    // Setup the wake up interrupt.
    CHECK_STATUS_OK(aon_timer_testutils_wakeup_config(aon_timer, count_cycles));
  } else {
    // Change the default value since the expectation is different.
    irq = kDifAonTimerIrqWkupTimerExpired;
    // Setup the wdog bark interrupt.
    CHECK_STATUS_OK(
        aon_timer_testutils_watchdog_config(aon_timer,
                                            /*bark_cycles=*/count_cycles,
                                            /*bite_cycles=*/count_cycles * 4,
                                            /*pause_in_sleep=*/false));
  }
  // Capture the current tick to measure the time the IRQ will take.
  uint32_t start_tick = (uint32_t)tick_count_get();
  uint32_t time_elapsed = 0;

  // Disable interrupts to be certain interrupt doesn't occur between while
  // condition check and `wait_for_interrupt` (so WFI misses that interrupt).
  irq_global_ctrl(false);

  // Only enter WFI loop if we haven't already seen the interrupt.
  if (peripheral != kTopEarlgreyPlicPeripheralAonTimerAon) {
    do {
      wait_for_interrupt();
      // WFI ignores global interrupt enable, so enable it now and then
      // immediately disable it. If there is an interrupt pending it will be
      // taken here between the enable and disable. This confines the interrupt
      // to a known place avoiding missed wakeup issues.
      irq_global_ctrl(true);
      irq_global_ctrl(false);
      time_elapsed = (uint32_t)irq_tick - start_tick;
    } while (peripheral != kTopEarlgreyPlicPeripheralAonTimerAon &&
             time_elapsed < sleep_range_h);
  }

  CHECK(time_elapsed < sleep_range_h && time_elapsed > sleep_range_l,
        "Timer took %u usec which is not in the range %u usec and %u usec",
        (uint32_t)time_elapsed, (uint32_t)sleep_range_l,
        (uint32_t)sleep_range_h);

  CHECK(peripheral == kTopEarlgreyPlicPeripheralAonTimerAon,
        "Interrupt from incorrect peripheral: exp = %d, obs = %d",
        kTopEarlgreyPlicPeripheralAonTimerAon, peripheral);

  CHECK(irq == expected_irq, "Interrupt type incorrect: exp = %d, obs = %d",
        kDifAonTimerIrqWkupTimerExpired, irq);

  LOG_INFO("Test completed in %u us", (uint32_t)irq_time_us);
}

/**
 * External interrupt handler.
 */
void ottf_external_isr(void) {
  // Calc the elapsed time since the activation of the IRQ.
  irq_tick = tick_count_get();

  dif_rv_plic_irq_id_t irq_id;
  CHECK_DIF_OK(dif_rv_plic_irq_claim(&plic, kPlicTarget, &irq_id));

  peripheral = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[irq_id];

  if (peripheral == kTopEarlgreyPlicPeripheralAonTimerAon) {
    irq =
        (dif_aon_timer_irq_t)(irq_id -
                              (dif_rv_plic_irq_id_t)
                                  kTopEarlgreyPlicIrqIdAonTimerAonWkupTimerExpired);

    if (irq_id == kTopEarlgreyPlicIrqIdAonTimerAonWkupTimerExpired) {
      CHECK_DIF_OK(dif_aon_timer_wakeup_stop(&aon_timer));
    } else if (irq_id == kTopEarlgreyPlicIrqIdAonTimerAonWdogTimerBark) {
      CHECK_DIF_OK(dif_aon_timer_watchdog_stop(&aon_timer));
    }

    CHECK_DIF_OK(dif_aon_timer_irq_acknowledge(&aon_timer, irq));
  }

  // Complete the IRQ by writing the IRQ source to the Ibex specific CC.
  // register
  CHECK_DIF_OK(dif_rv_plic_irq_complete(&plic, kPlicTarget, irq_id));
}

/**
 * OTTF external NMI internal IRQ handler.
 * The ROM configures the watchdog to generates a NMI at bark, so we clean the
 * NMI and wait the external irq handler next.
 */
void ottf_external_nmi_handler(void) {
  bool is_pending;
  // The watchdog bark external interrupt is also connected to the NMI input
  // of rv_core_ibex. We therefore expect the interrupt to be pending on the
  // peripheral side (the check is done later in the test function).
  CHECK_DIF_OK(dif_aon_timer_irq_is_pending(
      &aon_timer, kDifAonTimerIrqWdogTimerBark, &is_pending));
  CHECK_DIF_OK(dif_aon_timer_watchdog_stop(&aon_timer));
  // In order to handle the NMI we need to acknowledge the interrupt status
  // bit it at the peripheral side.
  CHECK_DIF_OK(
      dif_aon_timer_irq_acknowledge(&aon_timer, kDifAonTimerIrqWdogTimerBark));

  CHECK_DIF_OK(dif_rv_core_ibex_clear_nmi_state(&rv_core_ibex,
                                                kDifRvCoreIbexNmiSourceAll));
}

bool test_main(void) {
  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  // Initialize the rv timer to compute the tick.
  tick_init();

  // Initialize aon timer.
  CHECK_DIF_OK(dif_aon_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR), &aon_timer));

  CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  // Initialize the PLIC.
  mmio_region_t plic_base_addr =
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_plic_init(plic_base_addr, &plic));

  // Enable all the AON interrupts used in this test.
  rv_plic_testutils_irq_range_enable(
      &plic, kPlicTarget, kTopEarlgreyPlicIrqIdAonTimerAonWkupTimerExpired,
      kTopEarlgreyPlicIrqIdAonTimerAonWdogTimerBark);

  // Executing the test using random time bounds calculated from the clock
  // frequency to make sure the aon timer is generating the interrupt after the
  // chosen time and there's no error in the reference time measurement. This
  // calculation is required as the various platforms used for testing have
  // differing clocks frequencies. A minimum amount of cycles is required for
  // the interrupt to note the elapsed time so the test fails with an
  // unacceptable time variance when the sleep time is too low.
  enum {
    kMinCycles = 30 * 1000,
    kMaxCycles = 45 * 1000,
  };
  uint64_t low_time_range =
      udiv64_slow(kMinCycles * (uint64_t)1000000, kClockFreqCpuHz, NULL);
  uint64_t high_time_range =
      udiv64_slow(kMaxCycles * (uint64_t)1000000, kClockFreqCpuHz, NULL);

  // no error in the reference time measurement.
  uint64_t irq_time = rand_testutils_gen32_range((uint32_t)low_time_range,
                                                 (uint32_t)high_time_range);
  execute_test(&aon_timer, irq_time,
               /*expected_irq=*/kDifAonTimerIrqWkupTimerExpired);

  irq_time = rand_testutils_gen32_range((uint32_t)low_time_range,
                                        (uint32_t)high_time_range);
  execute_test(&aon_timer, irq_time,
               /*expected_irq=*/kDifAonTimerIrqWdogTimerBark);

  return true;
}
