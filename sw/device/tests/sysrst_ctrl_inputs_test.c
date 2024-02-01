// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_sysrst_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/sysrst_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_utils.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/* We need control flow for the ujson messages exchanged
 * with the host in OTTF_WAIT_FOR on real devices. */
OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

static dif_sysrst_ctrl_t sysrst_ctrl;
const uint32_t kNumPhases = 10;

// On DV, we must use variables in flash but on a real device,
// we must use variables in RAM.
static const volatile uint8_t kTestPhaseDV = 0;
static const volatile uint8_t kTestExpectedDV = 0;
// In DV, the sequence can ensure that the pins are set even before the test
// runs. On a real device, this is not the case and if the initial value of
// kTestPhase is 0, the very first OTTF_WAIT_FOR could succeed before the host
// can set the pins. To avoid this, and only on real devices, set the initial
// value to an invalid value so that we have to wait for the host.
static volatile uint8_t kTestPhaseReal = 0xff;
static volatile uint8_t kTestExpectedReal = 0;

enum {
  kOutputNumPads = 0x8,
  kOutputNumMioPads = 0x6,
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
    kTopEarlgreyPinmuxInselIob8, kTopEarlgreyPinmuxInselIor13,
    kTopEarlgreyPinmuxInselIoc7, kTopEarlgreyPinmuxInselIoc9,
};

// We need different pins on the hyperdebug boards since certain
// pins are not routed to the hyperdebug.
static const dif_pinmux_index_t kInputPadsReal[] = {
    kTopEarlgreyPinmuxInselIor10, kTopEarlgreyPinmuxInselIor11,
    kTopEarlgreyPinmuxInselIor12, kTopEarlgreyPinmuxInselIor5,
    kTopEarlgreyPinmuxInselIor6,  kTopEarlgreyPinmuxInselIor7,
};

static const dif_sysrst_ctrl_pin_t kSysrstCtrlInputs[] = {
    kDifSysrstCtrlPinKey0In,           kDifSysrstCtrlPinKey1In,
    kDifSysrstCtrlPinKey2In,           kDifSysrstCtrlPinPowerButtonIn,
    kDifSysrstCtrlPinAcPowerPresentIn, kDifSysrstCtrlPinLidOpenIn,
    kDifSysrstCtrlPinEcResetInOut,     kDifSysrstCtrlPinFlashWriteProtectInOut,
};

static uint8_t read_input_pins(void) {
  bool input_value;
  uint8_t inputs = 0;
  for (int i = 0; i < kOutputNumPads; ++i) {
    CHECK_DIF_OK(dif_sysrst_ctrl_input_pin_read(
        &sysrst_ctrl, kSysrstCtrlInputs[i], &input_value));
    inputs |= input_value << i;
  }
  return inputs;
}

bool test_main(void) {
  CHECK_DIF_OK(dif_sysrst_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SYSRST_CTRL_AON_BASE_ADDR),
      &sysrst_ctrl));

  dif_pinmux_t pinmux;
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));

  /* On real devices, we also need to configure the DIO pins */
  if (kDeviceType != kDeviceSimDV) {
    sysrst_ctrl_testutils_setup_dio(&pinmux);
    // Release pins so the host can control them.
    sysrst_ctrl_testutils_release_dio(&sysrst_ctrl, true, true);
    // Disable the EC reset pulse so that it does not interfere with the test.
    sysrst_ctrl_testutils_set_ec_rst_pulse_width(&sysrst_ctrl, 0);
  }
  const dif_pinmux_index_t *kInputPads =
      kDeviceType == kDeviceSimDV ? kInputPadsDV : kInputPadsReal;
  for (int i = 0; i < kOutputNumMioPads; ++i) {
    CHECK_DIF_OK(
        dif_pinmux_input_select(&pinmux, kPeripheralInputs[i], kInputPads[i]));
  }

  const uint32_t kTestPhaseTimeoutUsec =
      kDeviceType == kDeviceSimDV ? 10 : 1000000;
  // See explanation at the top of this file.
  const volatile uint8_t *kTestPhase =
      kDeviceType == kDeviceSimDV ? &kTestPhaseDV : &kTestPhaseReal;
  const volatile uint8_t *kTestExpected =
      kDeviceType == kDeviceSimDV ? &kTestExpectedDV : &kTestExpectedReal;

  for (int i = 0; i < kNumPhases; ++i) {
    OTTF_WAIT_FOR(i == *kTestPhase, kTestPhaseTimeoutUsec);
    uint8_t input_pins = read_input_pins();
    LOG_INFO("Expect pins: %x, got: %x", *kTestExpected, input_pins);
    CHECK(*kTestExpected == input_pins);
    // Test status set to InTest then Wfi for testbench synchronization,
    // an actual WFI instruction is not issued.
    test_status_set(kTestStatusInTest);
    test_status_set(kTestStatusInWfi);
  }

  test_status_set(kTestStatusInTest);
  return true;
}
