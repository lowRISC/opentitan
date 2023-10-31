// Copyright lowRISC contributors.
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

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

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
  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));

  // Initialize sysrst_ctrl.
  CHECK_DIF_OK(dif_sysrst_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SYSRST_CTRL_AON_BASE_ADDR),
      &sysrst_ctrl_aon));

  // Initialize rstmgr to check the reset reason.
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));
}

/**
 * Configure the sysrst.
 */
static void config_sysrst(const dif_pwrmgr_t *pwrmgr,
                          const dif_sysrst_ctrl_t *sysrst_ctrl_aon) {
  LOG_INFO("sysrst enabled");

  // Set sysrst as a reset source.
  CHECK_DIF_OK(dif_pwrmgr_set_request_sources(pwrmgr, kDifPwrmgrReqTypeReset,
                                              kDifPwrmgrResetRequestSourceOne,
                                              kDifToggleEnabled));
  LOG_INFO("Reset Request SourceOne is set");

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
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));

  CHECK_DIF_OK(dif_sysrst_ctrl_input_change_detect_configure(
      sysrst_ctrl_aon, sysrst_ctrl_input_change_config));

  CHECK_DIF_OK(dif_pinmux_input_select(
      &pinmux, kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonKey0In,
      kTopEarlgreyPinmuxInselIor13));
}

static void normal_sleep_por(const dif_pwrmgr_t *pwrmgr) {
  // Place device into low power and immediately wake.
  dif_pwrmgr_domain_config_t config;
  config = kDifPwrmgrDomainOptionUsbClockInLowPower |
           kDifPwrmgrDomainOptionCoreClockInLowPower |
           kDifPwrmgrDomainOptionIoClockInLowPower |
           kDifPwrmgrDomainOptionMainPowerInLowPower;

  // Program the pwrmgr to go to deep sleep state (clocks off).
  CHECK_STATUS_OK(pwrmgr_testutils_enable_low_power(pwrmgr, 0, config));
  LOG_INFO("Ready for pad POR");
  // Enter in low power mode.
  wait_for_interrupt();
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
    normal_sleep_por(&pwrmgr);
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
