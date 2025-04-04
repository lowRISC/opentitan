// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <limits.h>
#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_sysrst_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/FreeRTOSConfig.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

static const dt_rstmgr_t kRstmgrDt = 0;
static_assert(kDtRstmgrCount == 1, "this test expects a rstmgr");
static const dt_pwrmgr_t kPwrmgrDt = 0;
static_assert(kDtPwrmgrCount == 1, "this test expects a pwrmgr");
static const dt_sysrst_ctrl_t kSysrstCtrlDt = 0;
static_assert(kDtSysrstCtrlCount == 1, "this test expects a sysrst_ctrl");
static const dt_pinmux_t kPinmuxDt = 0;
static_assert(kDtPinmuxCount == 1, "this test expects a pinmux");

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

/**
 * Objects to access the peripherals used in this test via dif API.
 */
static dif_pwrmgr_t pwrmgr;
static dif_sysrst_ctrl_t sysrst_ctrl_aon;
static dif_rstmgr_t rstmgr;

/**
 * Initialize the peripherals used in this test.
 */
void init_peripherals(void) {
  // Initialize pwrmgr.
  CHECK_DIF_OK(dif_pwrmgr_init_from_dt(kPwrmgrDt, &pwrmgr));

  // Initialize sysrst_ctrl.
  CHECK_DIF_OK(dif_sysrst_ctrl_init_from_dt(kSysrstCtrlDt, &sysrst_ctrl_aon));

  // Initialize rstmgr to check the reset reason.
  CHECK_DIF_OK(dif_rstmgr_init_from_dt(kRstmgrDt, &rstmgr));
}

/**
 * Configure the sysrst.
 */
static void config_sysrst(const dif_pwrmgr_t *pwrmgr,
                          const dif_sysrst_ctrl_t *sysrst_ctrl_aon) {
  LOG_INFO("sysrst enabled");

  // Set sysrst as a reset source.
  dif_pwrmgr_request_sources_t reset_sources;
  CHECK_DIF_OK(dif_pwrmgr_find_request_source(
      pwrmgr, kDifPwrmgrReqTypeReset, dt_sysrst_ctrl_instance_id(kSysrstCtrlDt),
      kDtSysrstCtrlResetReqRstReq, &reset_sources));
  CHECK_DIF_OK(dif_pwrmgr_set_request_sources(
      pwrmgr, kDifPwrmgrReqTypeReset, reset_sources, kDifToggleEnabled));
  LOG_INFO("syrst_ctrl Reset Request is set");

  // Configure sysrst key combo
  // reset pulse : 50 us
  // detect durration : 50 us

  dif_sysrst_ctrl_key_combo_config_t sysrst_ctrl_key_combo_config = {
      .keys = kDifSysrstCtrlKeyAll,
      .detection_time_threshold = 10,
      .actions = kDifSysrstCtrlKeyComboActionAll,
      .embedded_controller_reset_duration = 10};

  CHECK_DIF_OK(dif_sysrst_ctrl_key_combo_detect_configure(
      sysrst_ctrl_aon, kDifSysrstCtrlKeyCombo0, sysrst_ctrl_key_combo_config));
  // Configure sysrst input change
  // debounce duration : 100 us
  dif_sysrst_ctrl_input_change_config_t sysrst_ctrl_input_change_config = {
      .input_changes = kDifSysrstCtrlInputAll, .debounce_time_threshold = 20};

  // Configure pinmux
  dif_pinmux_t pinmux;
  CHECK_DIF_OK(dif_pinmux_init_from_dt(kPinmuxDt, &pinmux));

  CHECK_DIF_OK(dif_sysrst_ctrl_input_change_detect_configure(
      sysrst_ctrl_aon, sysrst_ctrl_input_change_config));

  CHECK_DIF_OK(dif_pinmux_mio_select_input(
      &pinmux,
      dt_sysrst_ctrl_periph_io(kSysrstCtrlDt, kDtSysrstCtrlPeriphIoKey0In),
      kDtPadIor13));
}

static void low_power_por(const dif_pwrmgr_t *pwrmgr) {
  // Program the pwrmgr to go to deep sleep state (clocks off).
  CHECK_STATUS_OK(pwrmgr_testutils_enable_low_power(pwrmgr, 0, 0));
  LOG_INFO("Ready for pad POR");
  // Enter in low power mode.
  wait_for_interrupt();
  // If we arrive here the test must fail.
  CHECK(false, "Fail to enter in low power mode!");
}

bool test_main(void) {
  init_peripherals();

  // Check if there was a HW reset caused by expected cases
  dif_rstmgr_reset_info_bitfield_t rst_info;
  rst_info = rstmgr_testutils_reason_get();
  rstmgr_testutils_reason_clear();
  LOG_INFO("Reset info 0x%x", rst_info);
  if (rst_info == kDifRstmgrResetInfoPor) {
    config_sysrst(&pwrmgr, &sysrst_ctrl_aon);
    LOG_INFO("Setting sleep mode");
    low_power_por(&pwrmgr);
    CHECK(false, "This is unreachable");
  } else if ((rst_info & kDifRstmgrResetInfoSysRstCtrl) != 0) {
    // This means the host/sim_dv side found the POR case to work so all
    // went well.
    return true;
  } else {
    LOG_ERROR("Wrong reset reason %02X", rst_info);
  }
  return false;
}
