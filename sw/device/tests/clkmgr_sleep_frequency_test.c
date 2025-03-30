// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_sensor_ctrl.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/clkmgr_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/sensor_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "sw/device/lib/testing/autogen/isr_testutils.h"

OTTF_DEFINE_TEST_CONFIG();

/**
 * This test measure clock counts with clkmgr frequency measurements, performing
 * 100 measurements per round. Measurement errors (fast or slow clocks) are
 * recorded as recoverable error in clkmgr.
 *
 * After 100 measurements, test kicks in regular sleep with IO and USB
 * clocks turned off. Once the chip wakes up the measurements should be
 * enabled, but no errors should be found even for stopped clocks.
 */
enum {
  kWaitForCSRPollingMicros = 1,
  kMeasurementsPerRound = 100,
  kPlicTarget = 0,

};

static const dt_pwrmgr_t kPwrmgrDt = 0;
static_assert(kDtPwrmgrCount == 1, "this test expects a pwrmgr");
static const dt_aon_timer_t kAonTimerDt = 0;
static_assert(kDtAonTimerCount == 1, "this test expects an aon_timer");
static const dt_clkmgr_t kClkmgrDt = 0;
static_assert(kDtClkmgrCount == 1, "this test expects a clkmgr");
static const dt_sensor_ctrl_t kSensorCtrlDt = 0;
static_assert(kDtSensorCtrlCount >= 1, "this test expects a sensor_ctrl");
static const dt_rv_plic_t kRvPlicDt = 0;
static_assert(kDtRvPlicCount == 1, "this test expects a rv_plic");

static dif_clkmgr_t clkmgr;
static dif_pwrmgr_t pwrmgr;
static dif_rv_plic_t rv_plic;

static volatile bool isr_entered;

/**
 * External interrupt handler.
 */
bool ottf_handle_irq(uint32_t *exc_info, dt_instance_id_t devid,
                     dif_rv_plic_irq_id_t irq_id) {
  if (devid == dt_pwrmgr_instance_id(kPwrmgrDt) &&
      irq_id == dt_pwrmgr_irq_to_plic_id(kPwrmgrDt, kDtPwrmgrIrqWakeup)) {
    CHECK_DIF_OK(dif_pwrmgr_irq_acknowledge(&pwrmgr, kDtPwrmgrIrqWakeup));
    isr_entered = true;
    return true;
  } else {
    return false;
  }
}

bool test_main(void) {
  dif_sensor_ctrl_t sensor_ctrl;
  dif_aon_timer_t aon_timer;

  uint32_t delay_micros = 0;
  CHECK_STATUS_OK(aon_timer_testutils_get_us_from_aon_cycles(
      kMeasurementsPerRound, &delay_micros));

  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  CHECK_DIF_OK(dif_clkmgr_init_from_dt(kClkmgrDt, &clkmgr));
  CHECK_DIF_OK(dif_sensor_ctrl_init_from_dt(kSensorCtrlDt, &sensor_ctrl));
  CHECK_DIF_OK(dif_pwrmgr_init_from_dt(kPwrmgrDt, &pwrmgr));
  CHECK_DIF_OK(dif_aon_timer_init_from_dt(kAonTimerDt, &aon_timer));
  CHECK_DIF_OK(dif_rv_plic_init_from_dt(kRvPlicDt, &rv_plic));

  dif_pwrmgr_request_sources_t wakeup_sources;
  CHECK_DIF_OK(dif_pwrmgr_find_request_source(
      &pwrmgr, kDifPwrmgrReqTypeWakeup, dt_aon_timer_instance_id(kAonTimerDt),
      kDtAonTimerWakeupWkupReq, &wakeup_sources));

  LOG_INFO("TEST: wait for ast init");
  IBEX_SPIN_FOR(sensor_ctrl_ast_init_done(&sensor_ctrl), 1000);
  LOG_INFO("TEST: done ast init");

  CHECK(UNWRAP(pwrmgr_testutils_is_wakeup_reason(&pwrmgr, 0)) == true);

  CHECK_STATUS_OK(clkmgr_testutils_enable_clock_counts_with_expected_thresholds(
      &clkmgr, /*jitter_enabled=*/false, /*external_clk=*/false,
      /*low_speed=*/false));
  busy_spin_micros(delay_micros);

  // check results
  CHECK_STATUS_OK(clkmgr_testutils_check_measurement_counts(&clkmgr));
  CHECK_STATUS_OK(clkmgr_testutils_disable_clock_counts(&clkmgr));

  // Start new round of measurements.
  CHECK_STATUS_OK(clkmgr_testutils_enable_clock_counts_with_expected_thresholds(
      &clkmgr, /*jitter_enabled=*/false, /*external_clk=*/false,
      /*low_speed=*/false));

  busy_spin_micros(delay_micros);

  // Set wakeup timer to 100 us to have enough down time, and also wait before
  // entering sleep to have a chance to measure before sleeping. With normal
  // sleep all measurements should remain enabled, and there should be no
  // errors for clocks that were selectively turned off.
  uint64_t wakeup_threshold = kDeviceType == kDeviceSimVerilator ? 1000 : 100;
  CHECK_STATUS_OK(
      aon_timer_testutils_wakeup_config(&aon_timer, wakeup_threshold));

  // Enable all the AON interrupts used in this test.
  dif_rv_plic_irq_id_t irq_id =
      dt_pwrmgr_irq_to_plic_id(kPwrmgrDt, kDtPwrmgrIrqWakeup);
  rv_plic_testutils_irq_range_enable(&rv_plic, kPlicTarget, irq_id, irq_id);
  CHECK_DIF_OK(dif_pwrmgr_irq_set_enabled(&pwrmgr, 0, kDifToggleEnabled));

  // Put chip in normal sleep, and keep Core clock running. All io and usb
  // clocks are stopped, but we expect the stoppage won't trigger errors.
  CHECK_STATUS_OK(pwrmgr_testutils_enable_low_power(
      &pwrmgr, /*wakeups=*/wakeup_sources,
      /*domain_config=*/kDifPwrmgrDomainOptionCoreClockInLowPower |
          kDifPwrmgrDomainOptionUsbClockInActivePower |
          kDifPwrmgrDomainOptionMainPowerInLowPower));

  LOG_INFO("TEST: Issue WFI to enter sleep");
  wait_for_interrupt();

  CHECK(isr_entered);

  // Interrupt happened. Check the measurement state.
  CHECK_STATUS_OK(clkmgr_testutils_check_measurement_counts(&clkmgr));
  bool all_enabled = UNWRAP(
      clkmgr_testutils_check_measurement_enables(&clkmgr, kDifToggleEnabled));
  CHECK(all_enabled);

  return true;
}
