// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_sysrst_ctrl.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

static dif_pinmux_t pinmux;
static dif_sysrst_ctrl_t sysrst_ctrl;
static dif_pwrmgr_t pwrmgr;
static dif_rstmgr_t rstmgr;
static dif_flash_ctrl_state_t flash;
static dif_rstmgr_reset_info_bitfield_t rstmgr_reset_info;

const uint32_t kTestPhaseTimeoutUsec = 2500;

typedef enum {
  kTestPhaseSetup = 0,
  kTestPhaseCheckComboReset = 1,
  kTestPhaseOverrideSetup = 2,
  kTestPhaseOverrideZeros = 3,
  kTestPhaseOverrideOnes = 4,
  kTestPhaseDone = 5,
} test_phases_e;

enum {
  kAllZero = 0x0,
  kAllOne = 0xff,
  kLoopbackPartial = 0x5,
  kNumMioInputs = 0x4,
  kNumMioOutputs = 0x6,
  kOutputNumPads = 0x8,
};

static const dif_pinmux_index_t kPeripheralInputs[] = {
    kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonKey0In,
    kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonKey1In,
    kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonKey2In,
    kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonPwrbIn,
};

static const dif_pinmux_index_t kInputPads[] = {
    kTopEarlgreyPinmuxInselIob3,
    kTopEarlgreyPinmuxInselIob6,
    kTopEarlgreyPinmuxInselIob8,
    kTopEarlgreyPinmuxInselIor13,
};

static const dif_pinmux_index_t kPeripheralOutputs[] = {
    kTopEarlgreyPinmuxOutselSysrstCtrlAonKey0Out,
    kTopEarlgreyPinmuxOutselSysrstCtrlAonKey1Out,
    kTopEarlgreyPinmuxOutselSysrstCtrlAonKey2Out,
    kTopEarlgreyPinmuxOutselSysrstCtrlAonPwrbOut,
    kTopEarlgreyPinmuxOutselSysrstCtrlAonBatDisable,
    kTopEarlgreyPinmuxOutselSysrstCtrlAonZ3Wakeup,
};

static const dif_pinmux_index_t kOutputPads[] = {
    kTopEarlgreyPinmuxMioOutIob9, kTopEarlgreyPinmuxMioOutIor5,
    kTopEarlgreyPinmuxMioOutIor6, kTopEarlgreyPinmuxMioOutIoc7,
    kTopEarlgreyPinmuxMioOutIoc9, kTopEarlgreyPinmuxMioOutIob7,
};

static const dif_sysrst_ctrl_pin_t kSysrstCtrlOutputs[] = {
    kDifSysrstCtrlPinKey0Out,           kDifSysrstCtrlPinKey1Out,
    kDifSysrstCtrlPinKey2Out,           kDifSysrstCtrlPinPowerButtonOut,
    kDifSysrstCtrlPinBatteryDisableOut, kDifSysrstCtrlPinZ3WakeupOut,
    kDifSysrstCtrlPinEcResetInOut,      kDifSysrstCtrlPinFlashWriteProtectInOut,
};

// Threshold/Duration values are not specific to a real-world debounce
// scenario so are kept short to avoid excessive simulation time.
// Assuming a 5us aon clock period.
enum {
  kDetectionTimeThreshold = 1024,  // ~5ms
  kEcResetDuration = 512,          // ~2.5ms
  kDebounceTimeThreshold = 128,    // ~0.6ms
};

// Test phase written by testbench.
static volatile const test_phases_e kTestPhase = 0;

// Sets up the pinmux to assign input and output pads
// to the sysrst_ctrl peripheral as required.
static void pinmux_setup(void) {
  for (int i = 0; i < kNumMioInputs; ++i) {
    CHECK_DIF_OK(
        dif_pinmux_input_select(&pinmux, kPeripheralInputs[i], kInputPads[i]));
  }
  for (int i = 0; i < kNumMioOutputs; ++i) {
    CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kOutputPads[i],
                                          kPeripheralOutputs[i]));
  }
}

static void configure_combo_reset(void) {
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
  // Release the flash_wp signal
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

// Waits for the kTestPhase variable to be changed by a backdoor overwrite
// from the testbench in `chip_sw_sysrst_ctrl_ec_rst_l_vseq.sv`. This will
// indicate that the testbench is ready to proceed with the next phase of the
// test. The function `flash_ctrl_testutils_backdoor_wait_update` it's used to
// deal with possible caching that can prevent the software to read the new
// value of `kTestPhase`.
static void sync_with_testbench(void) {
  // Set WFI status for testbench synchronization,
  // no actual WFI instruction is issued.
  test_status_set(kTestStatusInWfi);
  test_status_set(kTestStatusInTest);
  CHECK_STATUS_OK(flash_ctrl_testutils_backdoor_wait_update(
      &flash, (uintptr_t)&kTestPhase, kTestPhaseTimeoutUsec));
}

// Enables the sysrst_ctrl overrides for the output pins. Allows
// both low and high override values.
static void override_setup(uint8_t pins_to_override) {
  for (int i = 0; i < kOutputNumPads; ++i) {
    if ((pins_to_override >> i) & 0x1) {
      CHECK_DIF_OK(dif_sysrst_ctrl_output_pin_override_set_enabled(
          &sysrst_ctrl, kSysrstCtrlOutputs[i], kDifToggleEnabled));
      CHECK_DIF_OK(dif_sysrst_ctrl_output_pin_override_set_allowed(
          &sysrst_ctrl, kSysrstCtrlOutputs[i], true, true));
    }
  }
}

// Sets the values of the output overrides as required.
static void set_output_overrides(uint8_t override_value) {
  for (int i = 0; i < kOutputNumPads; ++i) {
    CHECK_DIF_OK(dif_sysrst_ctrl_output_pin_set_override(
        &sysrst_ctrl, kSysrstCtrlOutputs[i], (override_value >> i) & 0x1));
  }
}

bool test_main(void) {
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  CHECK_DIF_OK(dif_sysrst_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SYSRST_CTRL_AON_BASE_ADDR),
      &sysrst_ctrl));
  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));

  CHECK_STATUS_OK(flash_ctrl_testutils_backdoor_init(&flash));

  pinmux_setup();
  rstmgr_reset_info = rstmgr_testutils_reason_get();

  // Disable EC rst override.
  CHECK_DIF_OK(dif_sysrst_ctrl_output_pin_override_set_enabled(
      &sysrst_ctrl, kDifSysrstCtrlPinEcResetInOut, kDifToggleDisabled));

  while (kTestPhase < kTestPhaseDone) {
    switch (kTestPhase) {
      case kTestPhaseSetup:
        CHECK(rstmgr_reset_info == kDifRstmgrResetInfoPor);
        configure_combo_reset();
        LOG_ERROR("We should have reset before this line.");
        break;
      case kTestPhaseCheckComboReset:
        CHECK(rstmgr_reset_info == kDifRstmgrResetInfoSysRstCtrl);
        break;
      case kTestPhaseOverrideSetup:
        override_setup(kAllOne);
        break;
      case kTestPhaseOverrideZeros:
        set_output_overrides(kAllZero);
        break;
      case kTestPhaseOverrideOnes:
        set_output_overrides(kAllOne);
        break;
      default:
        LOG_ERROR("Unexpected test phase : %d", kTestPhase);
        break;
    }
    sync_with_testbench();
  }
  return true;
}
