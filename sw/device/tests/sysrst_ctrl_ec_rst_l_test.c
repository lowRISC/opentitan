// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_sysrst_ctrl.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/sysrst_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/* We need control flow for the ujson messages exchanged
 * with the host in OTTF_WAIT_FOR on real devices. */
OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

static dif_pinmux_t pinmux;
static dif_sysrst_ctrl_t sysrst_ctrl;
static dif_pwrmgr_t pwrmgr;
static dif_rstmgr_t rstmgr;
static dif_rstmgr_reset_info_bitfield_t rstmgr_reset_info;

static const dt_pwrmgr_t kPwrmgrDt = 0;
static_assert(kDtPwrmgrCount == 1, "this test expects a pwrmgr");
static const dt_pinmux_t kPinmuxDt = 0;
static_assert(kDtPinmuxCount == 1, "this test expects a pinmux");
static const dt_rstmgr_t kRstmgrDt = 0;
static_assert(kDtRstmgrCount == 1, "this test expects a rstmgr");
static const dt_sysrst_ctrl_t kSysrstCtrlDt = 0;
static_assert(kDtSysrstCtrlCount == 1, "this test expects a sysrst_ctrl");

enum {
  kAllZero = 0x0,
  kAllOne = 0x3,
  kNumMioInputs = 0x2,
};

static const dif_pinmux_index_t kPeripheralInputs[] = {
    kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonKey0In,
    kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonKey1In,
};

static const dif_pinmux_index_t kInputPads[] = {
    kTopEarlgreyPinmuxInselIor6,
    kTopEarlgreyPinmuxInselIor7,
};

// Threshold/Duration values are not specific to a real-world debounce
// scenario so are kept short to avoid excessive simulation time.
// Assuming a 5us aon clock period.
enum {
  kDetectionTimeThreshold = 1024,  // ~5ms
  kEcResetStretchDurationMicros = 200 * 1000,
  kDebounceTimeThreshold = 128,  // ~0.6ms
};

// Sets up the pinmux to assign input and output pads
// to the sysrst_ctrl peripheral as required.
static void pinmux_setup(void) {
  for (int i = 0; i < kNumMioInputs; ++i) {
    CHECK_DIF_OK(
        dif_pinmux_input_select(&pinmux, kPeripheralInputs[i], kInputPads[i]));
  }
}

static void configure_combo_reset(void) {
  CHECK_DIF_OK(dif_sysrst_ctrl_key_combo_detect_configure(
      &sysrst_ctrl, kDifSysrstCtrlKeyCombo0,
      (dif_sysrst_ctrl_key_combo_config_t){
          .actions = kDifSysrstCtrlKeyComboActionSelfReset,
          .detection_time_threshold = kDetectionTimeThreshold,
          .embedded_controller_reset_duration = 0,
          .keys = kDifSysrstCtrlKey0 | kDifSysrstCtrlKey1}));
  // Use testutils to computes the value using the actual aon clock frequency.
  CHECK_DIF_OK(dif_sysrst_ctrl_input_change_detect_configure(
      &sysrst_ctrl, (dif_sysrst_ctrl_input_change_config_t){
                        .debounce_time_threshold = kDebounceTimeThreshold,
                        .input_changes = kDifSysrstCtrlInputKey0H2L |
                                         kDifSysrstCtrlInputKey1H2L}));
  // Prepare rstmgr for a reset with sysrst_ctrl.
  dif_pwrmgr_request_sources_t reset_sources;
  CHECK_DIF_OK(dif_pwrmgr_find_request_source(
      &pwrmgr, kDifPwrmgrReqTypeReset,
      dt_sysrst_ctrl_instance_id(kSysrstCtrlDt), kDtSysrstCtrlResetReqRstReq,
      &reset_sources));
  CHECK_STATUS_OK(rstmgr_testutils_pre_reset(&rstmgr));
  CHECK_DIF_OK(dif_pwrmgr_set_request_sources(
      &pwrmgr, kDifPwrmgrReqTypeReset, reset_sources, kDifToggleEnabled));
  // Issue WFI and wait for reset condition.
  LOG_INFO("wait for combo (key0&1 low)");
  test_status_set(kTestStatusInWfi);
  wait_for_interrupt();
}

bool test_main(void) {
  CHECK_DIF_OK(dif_pinmux_init_from_dt(kPinmuxDt, &pinmux));
  CHECK_DIF_OK(dif_sysrst_ctrl_init_from_dt(kSysrstCtrlDt, &sysrst_ctrl));
  CHECK_DIF_OK(dif_pwrmgr_init_from_dt(kPwrmgrDt, &pwrmgr));
  CHECK_DIF_OK(dif_rstmgr_init_from_dt(kRstmgrDt, &rstmgr));

  pinmux_setup();
  sysrst_ctrl_testutils_setup_dio(&pinmux);
  rstmgr_reset_info = rstmgr_testutils_reason_get();

  // On a POR, start the test: prepare the sysrst_ctrl with a combo to reset
  // the chip and wait for the host to reset the device using that combo.
  if (rstmgr_reset_info == kDifRstmgrResetInfoPor) {
    sysrst_ctrl_testutils_release_dio(&sysrst_ctrl, true, true);
    configure_combo_reset();
    LOG_ERROR("We should have reset before this line.");
  } else {
    // Otherwise, check that we got reset because of sysrst_ctrl.
    CHECK(rstmgr_reset_info == kDifRstmgrResetInfoSysRstCtrl);
    // Key0 is low since the reset was triggered by the combo. Wait until host
    // pulls key0 up.
    LOG_INFO("wait for key0 to go high");
    test_status_set(kTestStatusInWfi);
    bool key0_up = false;
    while (!key0_up) {
      CHECK_DIF_OK(dif_sysrst_ctrl_input_pin_read(
          &sysrst_ctrl, kDifSysrstCtrlPinKey0In, &key0_up));
    }
    // Release the pins
    LOG_INFO("releasing ec_rst and flash_wp");
    // Now release the pins.
    sysrst_ctrl_testutils_set_ec_rst_pulse_width(&sysrst_ctrl, 0);
    sysrst_ctrl_testutils_release_dio(&sysrst_ctrl, true, true);
    // Setup the EC reset stretch pulse width so that the host can check that it
    // works.
    sysrst_ctrl_testutils_set_ec_rst_pulse_width(&sysrst_ctrl,
                                                 kEcResetStretchDurationMicros);
    test_status_set(kTestStatusInWfi);
  }
  return true;
}
