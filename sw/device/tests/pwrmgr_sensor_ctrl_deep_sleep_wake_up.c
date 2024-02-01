// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/sim_dv/pwrmgr_sleep_all_wake_ups_impl.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "pwrmgr_regs.h"
#include "sw/device/lib/testing/autogen/isr_testutils.h"

/*
  PWRMGR SENSOR_CTRL SLEEP WAKE UP TEST

  This test runs power manager wake up from deep sleep mode to be woken
  up by sensor_ctrl via AST inputs.
 */

OTTF_DEFINE_TEST_CONFIG();

/**
 * Clean up pwrmgr wakeup reason register for the next round.
 */
static bool pwrmgr_wake_status_is_clear(void) {
  dif_pwrmgr_request_sources_t sources;
  CHECK_DIF_OK(dif_pwrmgr_get_current_request_sources(
      &pwrmgr, kDifPwrmgrReqTypeWakeup, &sources));
  return sources == 0;
}

static status_t wait_for_pwrmgr_wake_status_is_clear(void) {
  IBEX_TRY_SPIN_FOR(pwrmgr_wake_status_is_clear(), 20);
  return OK_STATUS();
}

bool test_main(void) {
  dif_pwrmgr_domain_config_t cfg;
  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  init_units();

  // Enable all the AON interrupts used in this test.
  rv_plic_testutils_irq_range_enable(&rv_plic, kTopEarlgreyPlicTargetIbex0,
                                     kTopEarlgreyPlicIrqIdPwrmgrAonWakeup,
                                     kTopEarlgreyPlicIrqIdPwrmgrAonWakeup);

  // Enable pwrmgr interrupt.
  CHECK_DIF_OK(dif_pwrmgr_irq_set_enabled(&pwrmgr, 0, kDifToggleEnabled));
  dif_pwrmgr_wakeup_reason_t wakeup_reason;
  CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_get(&pwrmgr, &wakeup_reason));

  if (wakeup_reason.request_sources == 0) {
    // This is a POR. Prepare to start the test.
    CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_clear(&pwrmgr));
    CHECK_DIF_OK(dif_pwrmgr_wakeup_request_recording_set_enabled(
        &pwrmgr, kDifToggleEnabled));

    CHECK_DIF_OK(dif_pwrmgr_get_domain_config(&pwrmgr, &cfg));
    cfg &= (kDifPwrmgrDomainOptionIoClockInLowPower |
            kDifPwrmgrDomainOptionUsbClockInLowPower |
            kDifPwrmgrDomainOptionUsbClockInActivePower);
    CHECK_STATUS_OK(pwrmgr_testutils_enable_low_power(
        &pwrmgr, kDifPwrmgrWakeupRequestSourceSix, cfg));
    LOG_INFO("Issue WFI to enter sensor_ctrl sleep");
    wait_for_interrupt();

    // This is not reachable.
    return false;
  } else if (wakeup_reason.types != kDifPwrmgrWakeupTypeRequest) {
    LOG_ERROR("Unexpected wakeup_reason.types 0x%x", wakeup_reason.types);
    return false;
  } else {
    // This is a reset from deep_sleep due to sensor_ctrl wakeup.
    LOG_INFO("Woke up by sensor_ctrl");
    dif_sensor_ctrl_events_t events;
    CHECK(!pwrmgr_wake_status_is_clear(), "Expected wake_status to be set");
    CHECK_DIF_OK(dif_sensor_ctrl_get_recov_events(&sensor_ctrl, &events));
    CHECK(events == 1, "Expected bit 0 to be set");
    CHECK_DIF_OK(dif_sensor_ctrl_clear_recov_event(&sensor_ctrl, 0));
    CHECK_DIF_OK(dif_sensor_ctrl_get_recov_events(&sensor_ctrl, &events));
    CHECK(events == 0, "Expected recoverable events to clear");
    CHECK_STATUS_OK(wait_for_pwrmgr_wake_status_is_clear(), 20);
    return true;
  }
}
