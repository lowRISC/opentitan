// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_sysrst_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/sysrst_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

OTTF_DEFINE_TEST_CONFIG();

static dif_pwrmgr_t pwrmgr;
static dif_rstmgr_t rstmgr;
static dif_sysrst_ctrl_t sysrst_ctrl;
static dif_gpio_t gpio;

static dif_pwrmgr_request_sources_t reset_sources, wakeup_sources,
    other_wakeup_sources;

static const dt_pwrmgr_t kPwrmgrDt = 0;
static_assert(kDtPwrmgrCount == 1, "this test expects a pwrmgr");
static const dt_pinmux_t kPinmuxDt = 0;
static_assert(kDtPinmuxCount == 1, "this test expects a pinmux");
static const dt_rstmgr_t kRstmgrDt = 0;
static_assert(kDtRstmgrCount == 1, "this test expects a rstmgr");
static const dt_gpio_t kGpioDt = 0;
static_assert(kDtGpioCount == 1, "this test expects a gpio");
static const dt_sysrst_ctrl_t kSysrstCtrlDt = 0;
static_assert(kDtSysrstCtrlCount == 1, "this test expects a sysrst_ctrl");

enum {
  kTestPhaseCheckComboReset = 0,
  kTestPhaseCheckDeepSleepWakeup = 1,
  kTestPhaseCheckDeepSleepReset = 2,
  kTestPhaseFinalCheck = 3,
};

// Threshold/Duration values are not specific to a real-world debounce
// scenario so are kept short to avoid excessive simulation time.
// Assuming a 5us aon clock period.
enum {
  kDetectionTimeThreshold = 1024,  // ~5ms
  kEcResetDuration = 512,          // ~2.5ms
  kDebounceTimeThreshold = 128,    // ~0.6ms
};

enum {
  kOutputNumMioPads = 6,
};

static const dt_sysrst_ctrl_periph_io_t kPeripheralInputs[] = {
    kDtSysrstCtrlPeriphIoKey0In,    kDtSysrstCtrlPeriphIoKey1In,
    kDtSysrstCtrlPeriphIoKey2In,    kDtSysrstCtrlPeriphIoPwrbIn,
    kDtSysrstCtrlPeriphIoAcPresent, kDtSysrstCtrlPeriphIoLidOpen,
};

static const dt_pad_t kInputPadsDV[] = {
    kDtPadIob3, kDtPadIob6, kDtPadIob8, kDtPadIob9, kDtPadIoc7, kDtPadIoc9,
};

// We need different pins on the hyperdebug boards since certain
// pins are not routed to the hyperdebug.
static const dt_pad_t kInputPadsReal[] = {
    kDtPadIor10, kDtPadIor11, kDtPadIor12, kDtPadIor5, kDtPadIor6, kDtPadIor7,
};

// On DV this device is in the flash and written by the testbench.
static volatile const uint8_t kTestPhaseDV = 0;
// Mask of the GPIOs used on the real device to read the test phase.
static const uint32_t kGpioMask = 0x3;

static void check_combo_reset(void) {
  CHECK_DIF_OK(dif_sysrst_ctrl_key_combo_detect_configure(
      &sysrst_ctrl, kDifSysrstCtrlKeyCombo0,
      (dif_sysrst_ctrl_key_combo_config_t){
          .actions = kDifSysrstCtrlKeyComboActionEcReset |
                     kDifSysrstCtrlKeyComboActionSelfReset,
          .detection_time_threshold = kDetectionTimeThreshold,
          .embedded_controller_reset_duration = kEcResetDuration,
          .keys = kDifSysrstCtrlKey0 | kDifSysrstCtrlKey1}));

  CHECK_DIF_OK(dif_sysrst_ctrl_input_change_detect_configure(
      &sysrst_ctrl, (dif_sysrst_ctrl_input_change_config_t){
                        .debounce_time_threshold = kDebounceTimeThreshold,
                        .input_changes = kDifSysrstCtrlInputKey0H2L |
                                         kDifSysrstCtrlInputKey1H2L}));
  CHECK_DIF_OK(dif_sysrst_ctrl_output_pin_override_configure(
      &sysrst_ctrl, kDifSysrstCtrlPinFlashWriteProtectInOut,
      (dif_sysrst_ctrl_pin_config_t){.allow_one = true,
                                     .allow_zero = true,
                                     .enabled = kDifToggleEnabled,
                                     .override_value = true}));
  // Prepare rstmgr for a reset with sysrst_ctrl (source one).
  CHECK_STATUS_OK(rstmgr_testutils_pre_reset(&rstmgr));
  CHECK_DIF_OK(dif_pwrmgr_set_request_sources(
      &pwrmgr, kDifPwrmgrReqTypeReset, reset_sources, kDifToggleEnabled));
  // Issue WFI and wait for reset condition.
  test_status_set(kTestStatusInWfi);
  wait_for_interrupt();
}

static void check_deep_sleep_wakeup(void) {
  CHECK_DIF_OK(dif_sysrst_ctrl_ulp_wakeup_configure(
      &sysrst_ctrl, (dif_sysrst_ctrl_ulp_wakeup_config_t){
                        .ac_power_debounce_time_threshold = 0,
                        .lid_open_debounce_time_threshold = 0,
                        .power_button_debounce_time_threshold = 0,
                        .enabled = kDifToggleEnabled}));
  // Setup low power.
  // Wakeup source is from sysrst_ctrl (source one).
  CHECK_STATUS_OK(rstmgr_testutils_pre_reset(&rstmgr));
  CHECK_STATUS_OK(
      pwrmgr_testutils_enable_low_power(&pwrmgr, wakeup_sources, 0));
  // Issue WFI and wait for reset condition.
  test_status_set(kTestStatusInWfi);
  wait_for_interrupt();
}

static void check_deep_sleep_reset(void) {
  CHECK_DIF_OK(dif_sysrst_ctrl_key_combo_detect_configure(
      &sysrst_ctrl, kDifSysrstCtrlKeyCombo1,
      (dif_sysrst_ctrl_key_combo_config_t){
          .actions = kDifSysrstCtrlKeyComboActionEcReset |
                     kDifSysrstCtrlKeyComboActionSelfReset,
          .detection_time_threshold = kDetectionTimeThreshold,
          .embedded_controller_reset_duration = kEcResetDuration,
          .keys = kDifSysrstCtrlKey2 | kDifSysrstCtrlKeyPowerButton}));
  CHECK_DIF_OK(dif_sysrst_ctrl_output_pin_override_configure(
      &sysrst_ctrl, kDifSysrstCtrlPinFlashWriteProtectInOut,
      (dif_sysrst_ctrl_pin_config_t){.allow_one = true,
                                     .allow_zero = true,
                                     .enabled = kDifToggleEnabled,
                                     .override_value = true}));
  CHECK_DIF_OK(dif_sysrst_ctrl_input_change_detect_configure(
      &sysrst_ctrl, (dif_sysrst_ctrl_input_change_config_t){
                        .debounce_time_threshold = kDebounceTimeThreshold,
                        .input_changes = kDifSysrstCtrlInputKey2H2L |
                                         kDifSysrstCtrlInputPowerButtonH2L}));
  // Setup low power.
  // Reset source is from sysrst_ctrl (source one).
  CHECK_STATUS_OK(rstmgr_testutils_pre_reset(&rstmgr));
  CHECK_DIF_OK(dif_pwrmgr_set_request_sources(
      &pwrmgr, kDifPwrmgrReqTypeReset, reset_sources, kDifToggleEnabled));
  // Enable low power with wakeup source other than
  // sysrst_ctrl (e.g. source two) as we don't want
  // a wakeup request but instead a reset.
  CHECK_STATUS_OK(
      pwrmgr_testutils_enable_low_power(&pwrmgr, other_wakeup_sources, 0));
  // Issue WFI and wait for reset condition.
  test_status_set(kTestStatusInWfi);
  wait_for_interrupt();
}

bool test_main(void) {
  CHECK_DIF_OK(dif_pwrmgr_init_from_dt(kPwrmgrDt, &pwrmgr));
  CHECK_DIF_OK(dif_rstmgr_init_from_dt(kRstmgrDt, &rstmgr));
  CHECK_DIF_OK(dif_sysrst_ctrl_init_from_dt(kSysrstCtrlDt, &sysrst_ctrl));
  CHECK_DIF_OK(dif_gpio_init_from_dt(kGpioDt, &gpio));

  CHECK_DIF_OK(dif_pwrmgr_find_request_source(
      &pwrmgr, kDifPwrmgrReqTypeWakeup,
      dt_sysrst_ctrl_instance_id(kSysrstCtrlDt), kDtSysrstCtrlWakeupWkupReq,
      &wakeup_sources));
  CHECK_DIF_OK(dif_pwrmgr_find_request_source(
      &pwrmgr, kDifPwrmgrReqTypeReset,
      dt_sysrst_ctrl_instance_id(kSysrstCtrlDt), kDtSysrstCtrlResetReqRstReq,
      &reset_sources));
  // Any wakeup source different from sysrst_ctrl.
  CHECK_DIF_OK(dif_pwrmgr_find_request_source(
      &pwrmgr, kDifPwrmgrReqTypeWakeup, dt_pinmux_instance_id(kPinmuxDt),
      kDtPinmuxWakeupPinWkupReq, &other_wakeup_sources));

  dif_rstmgr_reset_info_bitfield_t rstmgr_reset_info;
  rstmgr_reset_info = rstmgr_testutils_reason_get();

  dif_pinmux_t pinmux;
  CHECK_DIF_OK(dif_pinmux_init_from_dt(kPinmuxDt, &pinmux));
  const dt_pad_t *kInputPads =
      kDeviceType == kDeviceSimDV ? kInputPadsDV : kInputPadsReal;
  for (int i = 0; i < kOutputNumMioPads; ++i) {
    CHECK_DIF_OK(dif_pinmux_mio_select_input(
        &pinmux, dt_sysrst_ctrl_periph_io(kSysrstCtrlDt, kPeripheralInputs[i]),
        kInputPads[i]));
  }
  // On real devices, we also need to configure the DIO pins and two more pins
  // to read the test phase.
  if (kDeviceType != kDeviceSimDV) {
    sysrst_ctrl_testutils_setup_dio(&pinmux);
    CHECK_DIF_OK(dif_pinmux_mio_select_input(
        &pinmux, dt_gpio_periph_io(kGpioDt, kDtGpioPeriphIoGpio0), kDtPadIob0));
    CHECK_DIF_OK(dif_pinmux_mio_select_input(
        &pinmux, dt_gpio_periph_io(kGpioDt, kDtGpioPeriphIoGpio1), kDtPadIob1));
  }

  CHECK_DIF_OK(dif_sysrst_ctrl_output_pin_override_set_enabled(
      &sysrst_ctrl, kDifSysrstCtrlPinEcResetInOut, kDifToggleDisabled));

  // On real device, we cannot do backdoor writes the flash so we read the
  // test phase from GPIOs.
  uint8_t kTestPhase = kTestPhaseDV;
  if (kDeviceType != kDeviceSimDV) {
    uint32_t gpio_state;
    CHECK_DIF_OK(dif_gpio_read_all(&gpio, &gpio_state));
    kTestPhase = gpio_state & kGpioMask;
  }
  LOG_INFO("test phase: %u", kTestPhase);

  switch (kTestPhase) {
    case kTestPhaseCheckComboReset:
      CHECK(rstmgr_reset_info == kDifRstmgrResetInfoPor);
      check_combo_reset();
      break;
    case kTestPhaseCheckDeepSleepWakeup:
      CHECK(rstmgr_reset_info == kDifRstmgrResetInfoSysRstCtrl);
      check_deep_sleep_wakeup();
      break;
    case kTestPhaseCheckDeepSleepReset:
      CHECK(rstmgr_reset_info == kDifRstmgrResetInfoLowPowerExit);
      check_deep_sleep_reset();
      break;
    case kTestPhaseFinalCheck:
      CHECK(rstmgr_reset_info ==
            (kDifRstmgrResetInfoSysRstCtrl | kDifRstmgrResetInfoLowPowerExit));
      return true;
      break;
    default:
      LOG_ERROR("Unexpected test phase : %d", kTestPhase);
      break;
  }
  return false;
}
