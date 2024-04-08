// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_sysrst_ctrl.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/sysrst_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_utils.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/* We need control flow for the ujson messages exchanged
 * with the host in OTTF_WAIT_FOR on real devices. */
OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

// This is updated by the sv/host component of the test.
// On DV, we must use variables in flash but on a real device,
// we must use variables in RAM.
OT_SECTION(".rodata")
static volatile const uint8_t kTestPhaseDV[1];

static dif_pwrmgr_t pwrmgr;
static dif_rstmgr_t rstmgr;
static dif_pinmux_t pinmux;
static dif_sysrst_ctrl_t sysrst_ctrl;
static dif_flash_ctrl_state_t flash;
static dif_gpio_t gpio;

enum {
  kNumMioInPads = 3,
  kNumMioOutPads = 1,
  kTestPhaseTimeoutUsecDV = 500,
  kTestPhaseTimeoutUsecReal = 1000000,
  // This means 20 aon_clk ticks ~= 20 * 5 us = 100 us
  kDebounceTimer = 20,
};

enum {
  kTestPhaseInit = 0,
  kTestPhaseDriveInitial = 1,
  kTestPhaseWaitNoWakeup = 2,
  kTestPhaseWaitWakeup = 3,
  kTestPhaseDone = 4,
};

static const dif_pinmux_index_t kPeripheralInputs[] = {
    kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonPwrbIn,
    kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonAcPresent,
    kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonLidOpen,
};

static const dif_pinmux_index_t kInputPadsDV[] = {
    kTopEarlgreyPinmuxInselIor13,
    kTopEarlgreyPinmuxInselIoc7,
    kTopEarlgreyPinmuxInselIoc9,
};

static const dif_pinmux_index_t kInputPadsReal[] = {
    kTopEarlgreyPinmuxInselIor10,
    kTopEarlgreyPinmuxInselIor11,
    kTopEarlgreyPinmuxInselIor12,
};

static const dif_pinmux_index_t kPeripheralOutputs[] = {
    kTopEarlgreyPinmuxOutselSysrstCtrlAonZ3Wakeup,
};

static const dif_pinmux_index_t kOutputPadsDV[] = {
    kTopEarlgreyPinmuxMioOutIob7,
};

static const dif_pinmux_index_t kOutputPadsReal[] = {
    kTopEarlgreyPinmuxMioOutIor5,
};

// Mask of the GPIOs used on the real device to read the test phase.
static const uint32_t kGpioMask = 0x7;

/**
 * Sets up the pinmux to assign input and output pads to the sysrst_ctrl
 * peripheral as required.
 */
static void pinmux_setup(void) {
  const dif_pinmux_index_t *kInputPads =
      kDeviceType == kDeviceSimDV ? kInputPadsDV : kInputPadsReal;
  for (int i = 0; i < kNumMioInPads; ++i) {
    CHECK_DIF_OK(
        dif_pinmux_input_select(&pinmux, kPeripheralInputs[i], kInputPads[i]));
  }

  const dif_pinmux_index_t *kOutputPads =
      kDeviceType == kDeviceSimDV ? kOutputPadsDV : kOutputPadsReal;
  for (int i = 0; i < kNumMioOutPads; ++i) {
    CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kOutputPads[i],
                                          kPeripheralOutputs[i]));
  }
  sysrst_ctrl_testutils_setup_dio(&pinmux);
  sysrst_ctrl_testutils_release_dio(&sysrst_ctrl, true, true);
}

static uint8_t read_phase_pins(void) {
  uint32_t gpio_state;
  CHECK_DIF_OK(dif_gpio_read_all(&gpio, &gpio_state));
  // Since the host may not be able to change all pins atomically, we use
  // a Gray code encoding so that it suffices to change one pin to go to
  // the next phase.
  static const uint8_t kGrayCode[] = {0, 1, 3, 2, 7, 6, 4, 5};
  return kGrayCode[gpio_state & kGpioMask];
}

/**
 * Waits for `kTestPhase` variable to be changed by a backdoor overwrite
 * from the testbench in chip_sw_<testname>_vseq.sv. This will indicate that
 * the testbench is ready to proceed with the next phase of the test.
 *
 * Backdoor overwrites don't invalidate the read caches, so this explicitly
 * flushes them before updating the value.
 */
static status_t wait_next_test_phase(uint8_t prior_phase) {
  // Set WFI status for testbench synchronization,
  // no actual WFI instruction is issued.
  test_status_set(kTestStatusInWfi);
  test_status_set(kTestStatusInTest);
  LOG_INFO("wait_next_test_phase after %d", prior_phase);
  if (kDeviceType == kDeviceSimDV) {
    status_t status = flash_ctrl_testutils_backdoor_wait_update(
        &kTestPhaseDV[0], prior_phase, kTestPhaseTimeoutUsecDV);
    if (status_ok(status)) {
      LOG_INFO("Read test phase 0x%x", kTestPhaseDV[0]);
    }
    return status;
  } else {
    IBEX_TRY_SPIN_FOR(read_phase_pins() != prior_phase,
                      kTestPhaseTimeoutUsecReal);
    return OK_STATUS();
  }
}

/**
 * Configure *_debounce_ctl and then enable ULP wakeup.
 */
static void configure_wakeup(void) {
  dif_sysrst_ctrl_ulp_wakeup_config_t wakeup_config;

  // Keep toggle disabled when writing debounce configuration
  wakeup_config.enabled = kDifToggleDisabled;
  wakeup_config.ac_power_debounce_time_threshold = kDebounceTimer;
  wakeup_config.lid_open_debounce_time_threshold = kDebounceTimer;
  wakeup_config.power_button_debounce_time_threshold = kDebounceTimer;

  CHECK_DIF_OK(
      dif_sysrst_ctrl_ulp_wakeup_configure(&sysrst_ctrl, wakeup_config));

  CHECK_DIF_OK(
      dif_sysrst_ctrl_ulp_wakeup_set_enabled(&sysrst_ctrl, kDifToggleEnabled));
}

static void go_to_sleep(void) {
  // Wakeup source is from sysrst_ctrl (source one).
  LOG_INFO("Going to sleep.");
  test_status_set(kTestStatusInWfi);
  CHECK_STATUS_OK(rstmgr_testutils_pre_reset(&rstmgr));
  CHECK_STATUS_OK(pwrmgr_testutils_enable_low_power(
      &pwrmgr, kDifPwrmgrWakeupRequestSourceOne,
      /*pwrmgr_domain_config=*/0));
  wait_for_interrupt();
}

static bool reset_is_low_power_exit(void) {
  dif_rstmgr_reset_info_bitfield_t rst_info = rstmgr_testutils_reason_get();
  rstmgr_testutils_reason_clear();
  return rst_info == kDifRstmgrResetInfoLowPowerExit;
}

static bool has_wakeup_happened(void) {
  bool wakeup_detected;
  CHECK_DIF_OK(
      dif_sysrst_ctrl_ulp_wakeup_get_status(&sysrst_ctrl, &wakeup_detected));
  return wakeup_detected;
}

bool test_main(void) {
  CHECK_DIF_OK(dif_sysrst_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SYSRST_CTRL_AON_BASE_ADDR),
      &sysrst_ctrl));
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));
  CHECK_DIF_OK(
      dif_gpio_init(mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR), &gpio));

  // In DV, we use flash backdoor writes to store the phase.
  if (kDeviceType == kDeviceSimDV) {
    CHECK_STATUS_OK(flash_ctrl_testutils_backdoor_init(&flash));
  }
  // On real devices, we cannot store it in RAM since the wakeup will erase
  // it so use three pins to read the test phase.
  else {
    CHECK_DIF_OK(dif_pinmux_input_select(
        &pinmux, kTopEarlgreyPinmuxPeripheralInGpioGpio0,
        kTopEarlgreyPinmuxInselIob0));
    CHECK_DIF_OK(dif_pinmux_input_select(
        &pinmux, kTopEarlgreyPinmuxPeripheralInGpioGpio1,
        kTopEarlgreyPinmuxInselIob1));
    CHECK_DIF_OK(dif_pinmux_input_select(
        &pinmux, kTopEarlgreyPinmuxPeripheralInGpioGpio2,
        kTopEarlgreyPinmuxInselIob2));
  }
  LOG_INFO("reset");

  while (true) {
    uint8_t current_test_phase =
        kDeviceType == kDeviceSimDV ? *kTestPhaseDV : read_phase_pins();
    LOG_INFO("Test phase %d", current_test_phase);
    switch (current_test_phase) {
      case kTestPhaseInit:
        pinmux_setup();
        break;
      case kTestPhaseDriveInitial:
        configure_wakeup();
        LOG_INFO("kTestPhaseDriveInitial");
        break;
      case kTestPhaseWaitNoWakeup:
        CHECK(!reset_is_low_power_exit());
        CHECK(!has_wakeup_happened());
        LOG_INFO("kTestPhaseWaitNoWakeup");
        go_to_sleep();
        break;
      case kTestPhaseWaitWakeup:
        CHECK(reset_is_low_power_exit());
        CHECK(has_wakeup_happened());
        LOG_INFO("kTestPhaseWaitWakeup");
        break;
      case kTestPhaseDone:
        // End of test.
        return true;
      default:
        LOG_ERROR("Unexpected test phase : %d", current_test_phase);
        LOG_INFO("END");
        break;
    }
    status_t status = wait_next_test_phase(current_test_phase);
    CHECK_STATUS_OK(status);
    if (!status_ok(status)) {
      return false;
    }
  }
  return true;
}
