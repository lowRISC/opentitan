// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "devicetables.h"  // Generated
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_sysrst_ctrl.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/sysrst_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_utils.h"

/* We need control flow for the ujson messages exchanged
 * with the host in OTTF_WAIT_FOR on real devices. */
OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

static dif_pinmux_t pinmux;
static const dt_sysrst_ctrl_t *kSysrstCtrlDt = &kDtSysrstCtrl[0];
static dif_sysrst_ctrl_t sysrst_ctrl;
static dif_flash_ctrl_state_t flash;

enum {
  kTestPhaseTimeoutUsecDV = 100,
  kTestPhaseTimeoutUsecReal = 1000000,
};

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

static const dt_sysrst_ctrl_pin_t kPeripheralInputs[] = {
    kDtSysrstCtrlPinKey0In,
    kDtSysrstCtrlPinKey1In,
    kDtSysrstCtrlPinKey2In,
    kDtSysrstCtrlPinPwrbIn,
};

static const dt_pad_index_t kInputPadsDV[] = {
    kDtPadIob3,
    kDtPadIob6,
    kDtPadIob8,
    kDtPadIor13,
};

static const dt_pad_index_t kInputPadsReal[] = {
    kDtPadIor10,
    kDtPadIor11,
    kDtPadIor12,
    kDtPadIor5,
};

static const dt_sysrst_ctrl_pin_t kPeripheralOutputs[] = {
    kDtSysrstCtrlPinKey0Out,    kDtSysrstCtrlPinKey1Out,
    kDtSysrstCtrlPinKey2Out,    kDtSysrstCtrlPinPwrbOut,
    kDtSysrstCtrlPinBatDisable, kDtSysrstCtrlPinZ3Wakeup,
};

static const dt_pad_index_t kOutputPadsDV[] = {
    kDtPadIob9, kDtPadIor5, kDtPadIor6, kDtPadIoc7, kDtPadIoc9, kDtPadIob7,
};
static const dt_pad_index_t kOutputPadsReal[] = {
    kDtPadIor6, kDtPadIor7, kDtPadIob0, kDtPadIob1, kDtPadIob2, kDtPadIob3,
};

static const dif_sysrst_ctrl_pin_t kSysrstCtrlOutputs[] = {
    kDifSysrstCtrlPinKey0Out,           kDifSysrstCtrlPinKey1Out,
    kDifSysrstCtrlPinKey2Out,           kDifSysrstCtrlPinPowerButtonOut,
    kDifSysrstCtrlPinBatteryDisableOut, kDifSysrstCtrlPinZ3WakeupOut,
    kDifSysrstCtrlPinEcResetInOut,      kDifSysrstCtrlPinFlashWriteProtectInOut,
};

// Test phase written by testbench/host.
// On DV, we must use variables in flash but on a real device,
// we must use variables in RAM.
OT_SECTION(".rodata")
static volatile const uint8_t kTestPhaseDV = 0;
OT_SECTION(".data")
static volatile const uint8_t kTestPhaseReal = kTestPhaseSetup;

// Sets up the pinmux to assign input and output pads
// to the sysrst_ctrl peripheral as required.
static void pinmux_setup(void) {
  /* On real devices, we also need to configure the DIO pins */
  if (kDeviceType != kDeviceSimDV) {
    sysrst_ctrl_testutils_setup_dio(&pinmux);
    // Release pins so the host can control them.
    sysrst_ctrl_testutils_release_dio(&sysrst_ctrl, true, true);
    // Disable the EC reset pulse so that it does not interfere with the test.
    sysrst_ctrl_testutils_set_ec_rst_pulse_width(&sysrst_ctrl, 0);
  }
  const dt_pad_index_t *kInputPads =
      kDeviceType == kDeviceSimDV ? kInputPadsDV : kInputPadsReal;
  for (int i = 0; i < kNumMioInputs; ++i) {
    // TODO introduce a dif function to do that in one line.
    dt_pin_t pin = dt_sysrst_ctrl_pin(kSysrstCtrlDt, kPeripheralInputs[i]);
    dt_pad_t pad = kDtPad[kInputPads[i]];
    CHECK_DIF_OK(dif_pinmux_mio_select_input(&pinmux, pin, pad));
  }
  const dif_pinmux_index_t *kOutputPads =
      kDeviceType == kDeviceSimDV ? kOutputPadsDV : kOutputPadsReal;
  for (int i = 0; i < kNumMioOutputs; ++i) {
    // TODO introduce a dif function to do that in one line.
    dt_pin_t pin = dt_sysrst_ctrl_pin(kSysrstCtrlDt, kPeripheralOutputs[i]);
    dt_pad_t pad = kDtPad[kOutputPads[i]];
    CHECK_DIF_OK(dif_pinmux_mio_select_output(&pinmux, pad, pin));
  }
}

// Waits for the kTestPhase variable to be changed by a backdoor overwrite
// from the testbench in `chip_sw_sysrst_ctrl_ec_rst_l_vseq.sv`. This will
// indicate that the testbench is ready to proceed with the next phase of the
// test. The function `flash_ctrl_testutils_backdoor_wait_update` is used to
// deal with possible caching that can prevent the software to read the new
// value of `kTestPhase` (in DV).
static void sync_with_testbench(uint8_t prior_phase) {
  // Set WFI status for testbench synchronization,
  // no actual WFI instruction is issued.
  test_status_set(kTestStatusInWfi);
  test_status_set(kTestStatusInTest);
  if (kDeviceType == kDeviceSimDV) {
    CHECK_STATUS_OK(flash_ctrl_testutils_backdoor_wait_update(
        &kTestPhaseDV, prior_phase, kTestPhaseTimeoutUsecDV));
  } else {
    OTTF_WAIT_FOR(prior_phase != kTestPhaseReal, kTestPhaseTimeoutUsecReal);
  }
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
  CHECK_DIF_OK(dif_sysrst_ctrl_init_from_dt(kSysrstCtrlDt, &sysrst_ctrl));
  if (kDeviceType == kDeviceSimDV) {
    CHECK_STATUS_OK(flash_ctrl_testutils_backdoor_init(&flash));
  }

  const volatile uint8_t *kTestPhase =
      kDeviceType == kDeviceSimDV ? &kTestPhaseDV : &kTestPhaseReal;
  uint8_t current_test_phase = *kTestPhase;
  while (current_test_phase < kTestPhaseDone) {
    LOG_INFO("Test phase %d", current_test_phase);
    switch (current_test_phase) {
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
        LOG_ERROR("Unexpected test phase : %d", *kTestPhase);
        break;
    }
    sync_with_testbench(current_test_phase);
    current_test_phase = *kTestPhase;
  }
  return true;
}
