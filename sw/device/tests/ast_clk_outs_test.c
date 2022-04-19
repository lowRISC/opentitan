// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/dif/dif_sensor_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/clkmgr_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/**
 * AST CLK OUTPUTS TEST
 *
 * This test measure 3 clock outputs from ast (sys, io and usb)
 * by clkmgr frequency measurements.
 * Frequency meaasurement assumes aon_clk frequency 200KHz.
 * Given that, measurement is done for 500 us which is equivalent
 * to 100 measurements.
 * If measurement detects error (fast, slow), it will be stored
 * as recoverable error in clkmgr.
 *
 * After 100 measurements, test kicks in low-power mode, where
 * 3 clocks are off and measurement should not report spurious errors.
 * Wake up timer is set 500us which gives about 500us deep sleep.
 *
 * Then dut wakes up and repeat another 100 measurements before
 * test finish.
 */
enum {
  kWaitForCSRPolling = 1,  // 1us
  // aon period : 5us
  // meaure for 100 of period
  kMeasurementDelayMicros = 500,
  // at lowpower mode, main/io/usb clocks are off after 40us
  kClockCoolDownTime = 40,
};
static dif_clkmgr_t clkmgr;
static dif_pwrmgr_t pwrmgr;

typedef struct expected_count_info {
  int count;
  int variability;
} expected_count_info_t;

// Due to u_sync_ref and valid in each measurement block,
// measurement cnt has 3 cycle offset.
// So variability becomes 1(calculated from spec) + 3 = 4.

static const expected_count_info_t kCountInfos[] = {
    {.count = 479, .variability = 4}, {.count = 239, .variability = 4},
    {.count = 119, .variability = 4}, {.count = 499, .variability = 4},
    {.count = 239, .variability = 4},
};

static void enable_clk_measure(void) {
  // Enable cycle count measurements to confirm the frequencies are correct.
  for (size_t i = 0; i < ARRAYSIZE(kCountInfos); ++i) {
    expected_count_info_t count_info = kCountInfos[i];
    clkmgr_testutils_enable_clock_count_measurement(
        &clkmgr, (dif_clkmgr_measure_clock_t)i,
        count_info.count - count_info.variability,
        count_info.count + count_info.variability);
  }

  // lock measurement controls
  CHECK_DIF_OK(dif_clkmgr_measure_ctrl_disable(&clkmgr));
}

static void check_measurement_counts(const dif_clkmgr_t *clkmgr) {
  dif_clkmgr_recov_err_codes_t err_codes;
  CHECK_DIF_OK(dif_clkmgr_recov_err_code_get_codes(clkmgr, &err_codes));
  if (err_codes != 0) {
    LOG_ERROR("Unexpected recoverable error codes 0x%x", err_codes);
  } else {
    LOG_INFO("Clock measurements are okay");
  }

  // clear recoverable errors
  CHECK_DIF_OK(dif_clkmgr_recov_err_code_clear_codes(clkmgr, ~0u));
}

bool test_main(void) {
  dif_sensor_ctrl_t sensor_ctrl;
  dif_aon_timer_t aon_timer;

  CHECK_DIF_OK(dif_clkmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR), &clkmgr));
  CHECK_DIF_OK(dif_sensor_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SENSOR_CTRL_BASE_ADDR), &sensor_ctrl));
  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));
  CHECK_DIF_OK(dif_aon_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR), &aon_timer));

  // enable usb clock after low power wake up
  if (pwrmgr_testutils_is_wakeup_reason(&pwrmgr,
                                        kDifPwrmgrWakeupRequestSourceFive)) {
    dif_pwrmgr_domain_config_t config =
        (kDifPwrmgrDomainOptionUsbClockInActivePower +
         kDifPwrmgrDomainOptionMainPowerInLowPower);

    CHECK_DIF_OK(
        dif_pwrmgr_set_domain_config(&pwrmgr, config, kDifToggleEnabled));
  }

  LOG_INFO("TEST: wait for ast init");
  dif_toggle_t init_st = kDifToggleDisabled;

  while (init_st == kDifToggleDisabled) {
    CHECK_DIF_OK(
        dif_sensor_ctrl_get_ast_init_done_status(&sensor_ctrl, &init_st));

    busy_spin_micros(kWaitForCSRPolling);
  }

  LOG_INFO("TEST: done ast init");

  if (pwrmgr_testutils_is_wakeup_reason(&pwrmgr, 0)) {
    // program 3 clock meausres
    enable_clk_measure();
    busy_spin_micros(kMeasurementDelayMicros);
    // check results
    check_measurement_counts(&clkmgr);

    // set wakeup timer to 500us to have enough down time
    // during the down time, all clock measurements are still enabled but
    // not suppose to report any errors
    uint32_t wakeup_threshold = kDeviceType == kDeviceSimVerilator ? 1000 : 100;
    aon_timer_testutils_wakeup_config(&aon_timer, wakeup_threshold);
    // go to low power
    LOG_INFO("TEST: start low power mode");
    pwrmgr_testutils_enable_low_power(&pwrmgr,
                                      kDifPwrmgrWakeupRequestSourceFive, 0);

    // Enter low power mode.
    LOG_INFO("TEST: Issue WFI to enter sleep");
    wait_for_interrupt();

  } else if (pwrmgr_testutils_is_wakeup_reason(
                 &pwrmgr, kDifPwrmgrWakeupRequestSourceFive)) {
    LOG_INFO("TEST: disable clock measures");
    clkmgr_testutils_disable_clock_count_measurements(&clkmgr);
    LOG_INFO("TEST: dummy measure");
    check_measurement_counts(&clkmgr);
    busy_spin_micros(kMeasurementDelayMicros);
    LOG_INFO("TEST: re-enable");
    enable_clk_measure();
    busy_spin_micros(kMeasurementDelayMicros);
    LOG_INFO("TEST: check");
    check_measurement_counts(&clkmgr);

    LOG_INFO("TEST: done");
    return true;
  } else {  // error
    dif_pwrmgr_wakeup_reason_t wakeup_reason;
    CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_get(&pwrmgr, &wakeup_reason));
    LOG_ERROR("Unexpected wakeup detected: type = %d, request_source = %d",
              wakeup_reason.types, wakeup_reason.request_sources);
    return false;
  }

  return false;
}
