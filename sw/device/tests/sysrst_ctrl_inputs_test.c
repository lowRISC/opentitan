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

static dif_sysrst_ctrl_t sysrst_ctrl;
const uint32_t kTestPhaseTimeoutUsec = 10;
const uint32_t kNumPhases = 10;

// Test phase and expected values written by testbench.
static volatile const uint8_t kTestPhase = 0;
static volatile const uint8_t kTestExpected = 0;

enum {
  kOutputNumPads = 0x8,
  kOutputNunMioPads = 0x6,
};

static const dif_pinmux_index_t kPeripheralInputs[] = {
    kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonKey0In,
    kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonKey1In,
    kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonKey2In,
    kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonPwrbIn,
    kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonAcPresent,
    kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonLidOpen,
};

static const dif_pinmux_index_t kInputPads[] = {
    kTopEarlgreyPinmuxInselIob3, kTopEarlgreyPinmuxInselIob6,
    kTopEarlgreyPinmuxInselIob8, kTopEarlgreyPinmuxInselIor13,
    kTopEarlgreyPinmuxInselIoc7, kTopEarlgreyPinmuxInselIoc9,
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

  for (int i = 0; i < kOutputNunMioPads; ++i) {
    CHECK_DIF_OK(
        dif_pinmux_input_select(&pinmux, kPeripheralInputs[i], kInputPads[i]));
  }
  for (int i = 0; i < kNumPhases; ++i) {
    IBEX_SPIN_FOR(i == kTestPhase, kTestPhaseTimeoutUsec);
    uint8_t input_pins = read_input_pins();
    CHECK(kTestExpected == input_pins);
    // Test status set to InTest then Wfi for testbench synchronization,
    // an actual WFI instruction is not issued.
    test_status_set(kTestStatusInTest);
    test_status_set(kTestStatusInWfi);
  }

  test_status_set(kTestStatusInTest);
  return true;
}
