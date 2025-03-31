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
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/sysrst_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_utils.h"

/* We need control flow for the ujson messages exchanged
 * with the host in OTTF_WAIT_FOR on real devices. */
OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

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

// This is updated by the sv/host component of the test.
// On DV, we must use variables in flash but on a real device,
// we must use variables in RAM.
OT_SECTION(".rodata")
static volatile const uint8_t kTestPhaseDV;

static dif_pwrmgr_t pwrmgr;
static dif_rstmgr_t rstmgr;
static dif_pinmux_t pinmux;
static dif_sysrst_ctrl_t sysrst_ctrl;
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

static const dt_sysrst_ctrl_periph_io_t kPeripheralInputs[] = {
    kDtSysrstCtrlPeriphIoPwrbIn,
    kDtSysrstCtrlPeriphIoAcPresent,
    kDtSysrstCtrlPeriphIoLidOpen,
};

static const dt_pad_t kInputPadsDV[] = {
    kDtPadIor13,
    kDtPadIoc7,
    kDtPadIoc9,
};

static const dt_pad_t kInputPadsReal[] = {
    kDtPadIor10,
    kDtPadIor11,
    kDtPadIor12,
};

static const dt_sysrst_ctrl_periph_io_t kPeripheralOutputs[] = {
    kDtSysrstCtrlPeriphIoZ3Wakeup,
};

static const dt_pad_t kOutputPadsDV[] = {
    kDtPadIob7,
};

static const dt_pad_t kOutputPadsReal[] = {
    kDtPadIor5,
};

// Mask of the GPIOs used on the real device to read the test phase.
static const uint32_t kGpioMask = 0x7;

/**
 * Sets up the pinmux to assign input and output pads to the sysrst_ctrl
 * peripheral as required.
 */
static void pinmux_setup(void) {
  const dt_pad_t *kInputPads =
      kDeviceType == kDeviceSimDV ? kInputPadsDV : kInputPadsReal;
  for (int i = 0; i < kNumMioInPads; ++i) {
    CHECK_DIF_OK(dif_pinmux_mio_select_input(
        &pinmux, dt_sysrst_ctrl_periph_io(kSysrstCtrlDt, kPeripheralInputs[i]),
        kInputPads[i]));
  }

  const dt_pad_t *kOutputPads =
      kDeviceType == kDeviceSimDV ? kOutputPadsDV : kOutputPadsReal;
  for (int i = 0; i < kNumMioOutPads; ++i) {
    CHECK_DIF_OK(dif_pinmux_mio_select_output(
        &pinmux, kOutputPads[i],
        dt_sysrst_ctrl_periph_io(kSysrstCtrlDt, kPeripheralOutputs[i])));
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
    IBEX_TRY_SPIN_FOR(OTTF_BACKDOOR_READ(kTestPhaseDV) != prior_phase,
                      kTestPhaseTimeoutUsecDV);
    LOG_INFO("Read test phase 0x%x", kTestPhaseDV);
  } else {
    IBEX_TRY_SPIN_FOR(read_phase_pins() != prior_phase,
                      kTestPhaseTimeoutUsecReal);
  }
  return OK_STATUS();
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
  // Wakeup source is from sysrst_ctrl.
  dif_pwrmgr_request_sources_t wakeup_sources;
  CHECK_DIF_OK(dif_pwrmgr_find_request_source(
      &pwrmgr, kDifPwrmgrReqTypeWakeup,
      dt_sysrst_ctrl_instance_id(kSysrstCtrlDt), kDtSysrstCtrlWakeupWkupReq,
      &wakeup_sources));

  LOG_INFO("Going to sleep.");
  test_status_set(kTestStatusInWfi);
  CHECK_STATUS_OK(rstmgr_testutils_pre_reset(&rstmgr));
  CHECK_STATUS_OK(
      pwrmgr_testutils_enable_low_power(&pwrmgr, wakeup_sources,
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
  CHECK_DIF_OK(dif_sysrst_ctrl_init_from_dt(kSysrstCtrlDt, &sysrst_ctrl));
  CHECK_DIF_OK(dif_pinmux_init_from_dt(kPinmuxDt, &pinmux));
  CHECK_DIF_OK(dif_pwrmgr_init_from_dt(kPwrmgrDt, &pwrmgr));
  CHECK_DIF_OK(dif_rstmgr_init_from_dt(kRstmgrDt, &rstmgr));
  CHECK_DIF_OK(dif_gpio_init_from_dt(kGpioDt, &gpio));

  // In DV, we use flash backdoor writes to store the phase.
  // On real devices, we cannot store it in RAM since the wakeup will erase
  // it so use three pins to read the test phase.
  if (kDeviceType != kDeviceSimDV) {
    CHECK_DIF_OK(dif_pinmux_mio_select_input(
        &pinmux, dt_gpio_periph_io(kGpioDt, kDtGpioPeriphIoGpio0), kDtPadIob0));
    CHECK_DIF_OK(dif_pinmux_mio_select_input(
        &pinmux, dt_gpio_periph_io(kGpioDt, kDtGpioPeriphIoGpio1), kDtPadIob1));
    CHECK_DIF_OK(dif_pinmux_mio_select_input(
        &pinmux, dt_gpio_periph_io(kGpioDt, kDtGpioPeriphIoGpio2), kDtPadIob2));
  }
  LOG_INFO("reset");

  while (true) {
    uint8_t current_test_phase =
        kDeviceType == kDeviceSimDV ? kTestPhaseDV : read_phase_pins();
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
