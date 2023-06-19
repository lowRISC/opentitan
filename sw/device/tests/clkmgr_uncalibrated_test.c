// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_sensor_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/clkmgr_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/sensor_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"

OTTF_DEFINE_TEST_CONFIG();

/**
 * AST CLK OUTPUTS TEST
 *
 * This test measures clock counts with clkmgr frequency measurements,
 * performing 100 measurements per round. Measurement errors (fast or slow
 * clocks) are recorded as recoverable error in clkmgr.
 *
 * After 100 measurements, this configures the clock counters per external
 * clock and low speed settings before entering low-power mode, where all but
 * the aon clock are off. The expectation is that main and io clocks will
 * report errors, but div2 and div4 should not.
 *
 * When the dut wakes up, another 100 measurements are done before the
 * test finishes.
 *
 * Notice the test overrides the hardware behavior so it comes out with
 * calibrated USB clock, otherwise the USB clock frequency will be incorrect.
 * USB calibration should be a separate test, and may be vendor-specific.
 */
enum {
  kWaitForCSRPollingUs = 1,  // 1us
  kMeasurementsPerRound = 100,
};

static dif_clkmgr_t clkmgr;
static dif_pwrmgr_t pwrmgr;

void check_ast_init_is_not_true(const dif_otp_ctrl_t *otp_ctrl) {
  ptrdiff_t reg_offset = OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET;
  reg_offset += OTP_CTRL_PARAM_CREATOR_SW_CFG_AST_INIT_EN_OFFSET;
  uint32_t enabled = mmio_region_read32(otp_ctrl->base_addr, reg_offset);
  LOG_INFO("ast_init enabled %d", enabled);
  CHECK(enabled != kMultiBitBool4True);
}

bool test_main(void) {
  dif_aon_timer_t aon_timer;
  dif_otp_ctrl_t otp_ctrl;
  dif_sensor_ctrl_t sensor_ctrl;

  uint32_t delay_micros = 0;
  CHECK_STATUS_OK(aon_timer_testutils_get_us_from_aon_cycles(
      kMeasurementsPerRound, &delay_micros));

  CHECK_DIF_OK(dif_aon_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR), &aon_timer));
  CHECK_DIF_OK(dif_clkmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR), &clkmgr));
  CHECK_DIF_OK(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp_ctrl));
  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));
  CHECK_DIF_OK(dif_sensor_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SENSOR_CTRL_BASE_ADDR), &sensor_ctrl));

  LOG_INFO("TEST uncalibrated clocks.");
  // Make sure the AST is NOT initialized.
  check_ast_init_is_not_true(&otp_ctrl);
  IBEX_SPIN_FOR(sensor_ctrl_ast_init_done(&sensor_ctrl), 1000);
  LOG_INFO("TEST: done ast init");

  if (UNWRAP(pwrmgr_testutils_is_wakeup_reason(&pwrmgr, 0)) == true) {
    // At POR.
    LOG_INFO("Run clock measurements right after POR");
    CHECK_STATUS_OK(
        clkmgr_testutils_enable_clock_counts_with_expected_thresholds(
            &clkmgr, /*jitter_enabled=*/false, /*external_clk=*/false,
            /*low_speed=*/false));
    busy_spin_micros(delay_micros);

    // check results
    CHECK_STATUS_OK(clkmgr_testutils_check_measurement_counts(&clkmgr));
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
