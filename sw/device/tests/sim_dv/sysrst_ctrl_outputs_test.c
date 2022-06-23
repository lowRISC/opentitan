// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_sysrst_ctrl.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

static dif_pinmux_t pinmux;
static dif_sysrst_ctrl_t sysrst_ctrl;

const uint32_t kTestPhaseTimeoutUsec = 100;

enum {
  kTestPhaseSetup = 0,
  kTestPhaseLoopback = 1,
  kTestPhaseOverrideSetup = 2,
  kTestPhaseOverrideZeros = 3,
  kTestPhaseOverrideOnes = 4,
  kTestPhaseOverrideRelease = 5,
  kTestPhaseOverrideAndLoopback = 6,
  kTestPhaseDone = 7,
};

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

// Test phase written by testbench.
static volatile const uint8_t kTestPhase = 0;

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

// Waits for the kTestPhase variable to be changed by a backdoor overwrite
// from the testbench in chip_sw_sysrst_ctrl_outputs_vseq.sv. This will
// indicate that the testbench is ready to proceed with the
// next phase of the test.
static void wait_next_test_phase(void) {
  uint8_t current_phase = kTestPhase;
  // Set WFI status for testbench synchronization,
  // no actual WFI instruction is issued.
  test_status_set(kTestStatusInWfi);
  test_status_set(kTestStatusInTest);
  IBEX_SPIN_FOR(current_phase != kTestPhase, kTestPhaseTimeoutUsec);
  LOG_INFO("Test phase = %0d", kTestPhase);
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

// Disables the overrides. Allows the outputs to pass-through the
// values from the relevant input pins.
static void override_disable(void) {
  for (int i = 0; i < kOutputNumPads; ++i) {
    CHECK_DIF_OK(dif_sysrst_ctrl_output_pin_override_set_enabled(
        &sysrst_ctrl, kSysrstCtrlOutputs[i], kDifToggleDisabled));
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

  while (kTestPhase < kTestPhaseDone) {
    switch (kTestPhase) {
      case kTestPhaseSetup:
        pinmux_setup();
        break;
      case kTestPhaseLoopback:
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
      case kTestPhaseOverrideRelease:
        override_disable();
        break;
      case kTestPhaseOverrideAndLoopback:
        override_setup(kLoopbackPartial);
        set_output_overrides(kLoopbackPartial);
        break;
      default:
        LOG_ERROR("Unexpected test phase : %d", kTestPhase);
        break;
    }
    wait_next_test_phase();
  }
  return true;
}
