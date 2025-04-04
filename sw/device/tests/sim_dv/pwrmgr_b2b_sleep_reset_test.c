// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_sysrst_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/nv_counter_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "aon_timer_regs.h"
/*
   PWRMGR BACK TO BACK DEEP SLEEP, RESET / WAKEUP TEST

   This test introduces reset or wakeup event close to (before or after)
   entering low power state.

   'kNumRound' is set to 10 by sv sequence (chip_sw_repeat_reset_wkup_vseq.sv)

   For the reset event, the sequence assert power on resets by driving POR_N
   PAD. For the wake up event, the sequence assert power button in by driving
   IOR13 PAD.

 */
OTTF_DEFINE_TEST_CONFIG();

static const dt_rstmgr_t kRstmgrDt = 0;
static_assert(kDtRstmgrCount == 1, "this test expects a rstmgr");
static const dt_pwrmgr_t kPwrmgrDt = 0;
static_assert(kDtPwrmgrCount == 1, "this test expects a pwrmgr");
static const dt_pinmux_t kPinmuxDt = 0;
static_assert(kDtPinmuxCount == 1, "this test expects exactly one pinmux");
static const dt_flash_ctrl_t kFlashCtrlDt = 0;
static_assert(kDtFlashCtrlCount >= 1,
              "this library expects at least one flash_ctrl");
static_assert(kDtSysrstCtrlCount >= 1,
              "this test expects at least one sysrst_ctrl");
static const dt_sysrst_ctrl_t kSysrstCtrlDt = 0;
static_assert(kDtAonTimerCount == 1, "this test expects an aon_timer");
static const dt_aon_timer_t kAonTimerDt = 0;

static volatile const uint8_t kNumRound;

static dif_flash_ctrl_state_t flash_ctrl;
static dif_sysrst_ctrl_t sysrst_ctrl;
static dif_pinmux_t pinmux;

/**
 * sysrst_ctrl config for test #1
 * . set sysrst_ctrl.KEY_INTR_CTL.pwrb_in_H2L to 1
 * . use IOR13 as pwrb_in
 */
static void prgm_push_button_wakeup(void) {
  dif_sysrst_ctrl_input_change_config_t config = {
      .input_changes = kDifSysrstCtrlInputPowerButtonH2L,
      .debounce_time_threshold = 1,  // 5us
  };
  CHECK_DIF_OK(
      dif_sysrst_ctrl_input_change_detect_configure(&sysrst_ctrl, config));
  CHECK_DIF_OK(dif_pinmux_mio_select_input(
      &pinmux,
      dt_sysrst_ctrl_periph_io(kSysrstCtrlDt, kDtSysrstCtrlPeriphIoPwrbIn),
      kDtPadIor13));
}

bool test_main(void) {
  // Issue a wakeup signal in ~1.5 ms through the AON timer.
  // This timer is needed when reset or  wakeup fail to
  // bring state machine back to active state.
  // This can happen when wake up event comes before low power
  // entry event.
  uint64_t wakeup_threshold = kDeviceType == kDeviceSimVerilator ? 3000 : 300;

  // Initialize pwrmgr
  dif_pwrmgr_t pwrmgr;
  CHECK_DIF_OK(dif_pwrmgr_init_from_dt(kPwrmgrDt, &pwrmgr));

  // Initialize rstmgr since this will check some registers.
  dif_rstmgr_t rstmgr;
  CHECK_DIF_OK(dif_rstmgr_init_from_dt(kRstmgrDt, &rstmgr));

  // Initialize flash_ctrl
  CHECK_DIF_OK(dif_flash_ctrl_init_state_from_dt(&flash_ctrl, kFlashCtrlDt));

  // Initialize sysrst_ctrl
  CHECK_DIF_OK(dif_sysrst_ctrl_init_from_dt(kSysrstCtrlDt, &sysrst_ctrl));

  // Initialize pinmux
  CHECK_DIF_OK(dif_pinmux_init_from_dt(kPinmuxDt, &pinmux));

  // First check the flash stored value
  uint32_t event_idx = 0;
  CHECK_STATUS_OK(flash_ctrl_testutils_counter_get(0, &event_idx));
  // Enable flash access
  CHECK_STATUS_OK(
      flash_ctrl_testutils_default_region_access(&flash_ctrl,
                                                 /*rd_en*/ true,
                                                 /*prog_en*/ true,
                                                 /*erase_en*/ true,
                                                 /*scramble_en*/ false,
                                                 /*ecc_en*/ false,
                                                 /*he_en*/ false));

  // Increment flash counter to know where we are
  CHECK_STATUS_OK(flash_ctrl_testutils_counter_increment(&flash_ctrl, 0));

  // Read wakeup reason before check
  dif_pwrmgr_wakeup_reason_t wakeup_reason;
  CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_get(&pwrmgr, &wakeup_reason));
  LOG_INFO("wakeup type:%d   wakeup reason: 0x%02X", wakeup_reason.types,
           wakeup_reason.request_sources);

  dif_pwrmgr_request_sources_t pwrmgr_aon_timer_wakeups;
  CHECK_DIF_OK(dif_pwrmgr_find_request_source(
      &pwrmgr, kDifPwrmgrReqTypeWakeup, dt_aon_timer_instance_id(kAonTimerDt),
      kDtAonTimerWakeupWkupReq, &pwrmgr_aon_timer_wakeups));
  dif_pwrmgr_request_sources_t pwrmgr_sysrst_ctrl_wakeups;
  CHECK_DIF_OK(dif_pwrmgr_find_request_source(
      &pwrmgr, kDifPwrmgrReqTypeWakeup,
      dt_sysrst_ctrl_instance_id(kSysrstCtrlDt), kDtSysrstCtrlWakeupWkupReq,
      &pwrmgr_sysrst_ctrl_wakeups));
  dif_pwrmgr_request_sources_t pwrmgr_all_wakeups;
  CHECK_DIF_OK(dif_pwrmgr_get_all_request_sources(
      &pwrmgr, kDifPwrmgrReqTypeWakeup, &pwrmgr_all_wakeups));

  if (wakeup_reason.types == 0) {
    // POR reset
    CHECK(wakeup_reason.request_sources == 0);
  } else if (wakeup_reason.types == kDifPwrmgrWakeupTypeRequest) {
    // sysrst_ctrl or aon_timer
    CHECK(wakeup_reason.request_sources ==
          (pwrmgr_sysrst_ctrl_wakeups | pwrmgr_aon_timer_wakeups));
  } else {
    LOG_ERROR("unexpected wakeup_type: 0x%x", wakeup_reason.types);
  }

  // Read reset info  before check
  dif_rstmgr_reset_info_bitfield_t rst_info;
  rst_info = rstmgr_testutils_reason_get();
  rstmgr_testutils_reason_clear();
  LOG_INFO("reset info = 0x%02X", rst_info);

  if (rst_info != kDifRstmgrResetInfoPor &&
      rst_info != kDifRstmgrResetInfoLowPowerExit) {
    LOG_ERROR("unexpected reset info: 0x%x", rst_info);
  }

  dif_aon_timer_t aon_timer;
  CHECK_DIF_OK(dif_aon_timer_init_from_dt(kAonTimerDt, &aon_timer));

  // Status clean up
  if (event_idx > 0) {
    // aon timer clean up
    CHECK_DIF_OK(dif_aon_timer_wakeup_stop(&aon_timer));
    //    mmio_region_write32(
    //        mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR),
    //        AON_TIMER_WKUP_CAUSE_REG_OFFSET, 0);
    CHECK_DIF_OK(dif_aon_timer_clear_wakeup_cause(&aon_timer));
    // sysrst ctrl status clean up
    CHECK_DIF_OK(dif_sysrst_ctrl_ulp_wakeup_clear_status(&sysrst_ctrl));
  }

  if (event_idx < kNumRound) {
    LOG_INFO("Test round %d", event_idx);
  } else {
    LOG_INFO("Test finish");
    return true;
  }

  // pin mux / sysrst ctrl set up for push button wakeup
  prgm_push_button_wakeup();

  // Prepare rstmgr for a reset.
  CHECK_STATUS_OK(rstmgr_testutils_pre_reset(&rstmgr));

  // This is mark for sv sequence to prepare to asserting parallel event.
  LOG_INFO("ready for power down");
  busy_spin_micros(10);
  // timer setup in case wake up comes before entering low power mode
  CHECK_STATUS_OK(
      aon_timer_testutils_wakeup_config(&aon_timer, wakeup_threshold));

  // Deep sleep.
  CHECK_STATUS_OK(
      pwrmgr_testutils_enable_low_power(&pwrmgr, pwrmgr_all_wakeups, 0));

  // Enter low power mode.
  wait_for_interrupt();

  return false;
}
