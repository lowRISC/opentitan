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

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

static dif_pwrmgr_t pwrmgr;
static dif_rstmgr_t rstmgr;
static dif_sysrst_ctrl_t sysrst_ctrl;
static dif_gpio_t gpio;

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

static const dif_pinmux_index_t kPeripheralInputs[] = {
    kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonKey0In,
    kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonKey1In,
    kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonKey2In,
    kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonPwrbIn,
    kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonAcPresent,
    kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonLidOpen,
};

static const dif_pinmux_index_t kInputPadsDV[] = {
    kTopEarlgreyPinmuxInselIob3, kTopEarlgreyPinmuxInselIob6,
    kTopEarlgreyPinmuxInselIob8, kTopEarlgreyPinmuxInselIob9,
    kTopEarlgreyPinmuxInselIoc7, kTopEarlgreyPinmuxInselIoc9,
};

// We need different pins on the hyperdebug boards since certain
// pins are not routed to the hyperdebug.
static const dif_pinmux_index_t kInputPadsReal[] = {
    kTopEarlgreyPinmuxInselIor10, kTopEarlgreyPinmuxInselIor11,
    kTopEarlgreyPinmuxInselIor12, kTopEarlgreyPinmuxInselIor5,
    kTopEarlgreyPinmuxInselIor6,  kTopEarlgreyPinmuxInselIor7,
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
  CHECK_DIF_OK(dif_pwrmgr_set_request_sources(&pwrmgr, kDifPwrmgrReqTypeReset,
                                              kDifPwrmgrResetRequestSourceOne,
                                              kDifToggleEnabled));
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
  CHECK_STATUS_OK(pwrmgr_testutils_enable_low_power(
      &pwrmgr, kDifPwrmgrWakeupRequestSourceOne, 0));
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
  CHECK_DIF_OK(dif_pwrmgr_set_request_sources(&pwrmgr, kDifPwrmgrReqTypeReset,
                                              kDifPwrmgrResetRequestSourceOne,
                                              kDifToggleEnabled));
  // Enable low power with wakeup source other than
  // sysrst_ctrl (e.g. source two) as we don't want
  // a wakeup request but instead a reset.
  CHECK_STATUS_OK(pwrmgr_testutils_enable_low_power(
      &pwrmgr, kDifPwrmgrWakeupRequestSourceTwo, 0));
  // Issue WFI and wait for reset condition.
  test_status_set(kTestStatusInWfi);
  wait_for_interrupt();
}

bool test_main(void) {
  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));
  CHECK_DIF_OK(dif_sysrst_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SYSRST_CTRL_AON_BASE_ADDR),
      &sysrst_ctrl));
  CHECK_DIF_OK(
      dif_gpio_init(mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR), &gpio));

  dif_rstmgr_reset_info_bitfield_t rstmgr_reset_info;
  rstmgr_reset_info = rstmgr_testutils_reason_get();

  dif_pinmux_t pinmux;
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  const dif_pinmux_index_t *kInputPads =
      kDeviceType == kDeviceSimDV ? kInputPadsDV : kInputPadsReal;
  for (int i = 0; i < kOutputNumMioPads; ++i) {
    CHECK_DIF_OK(
        dif_pinmux_input_select(&pinmux, kPeripheralInputs[i], kInputPads[i]));
  }
  // On real devices, we also need to configure the DIO pins and two more pins
  // to read the test phase.
  if (kDeviceType != kDeviceSimDV) {
    sysrst_ctrl_testutils_setup_dio(&pinmux);
    CHECK_DIF_OK(dif_pinmux_input_select(
        &pinmux, kTopEarlgreyPinmuxPeripheralInGpioGpio0,
        kTopEarlgreyPinmuxInselIob0));
    CHECK_DIF_OK(dif_pinmux_input_select(
        &pinmux, kTopEarlgreyPinmuxPeripheralInGpioGpio1,
        kTopEarlgreyPinmuxInselIob1));
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
