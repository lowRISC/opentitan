// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_sensor_ctrl.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

dif_pwrmgr_t pwrmgr;
dif_rv_plic_t rv_plic;
dif_sensor_ctrl_t sensor_ctrl;

enum {
  kPlicTarget = 0,
};

static const dt_pwrmgr_t kPwrmgrDt = 0;
static_assert(kDtPwrmgrCount == 1, "this library expects exactly one pwrmgr");
static const dt_rv_plic_t kRvPlicDt = 0;
static_assert(kDtRvPlicCount == 1, "this library expects exactly one rv_plic");
static const dt_sensor_ctrl_t kSensorCtrlDt = 0;
static_assert(kDtSensorCtrlCount == 1,
              "this library expects exactly one sensor_ctrl");

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

/**
 * External interrupt handler.
 */
bool ottf_handle_irq(uint32_t *exc_info, dt_instance_id_t devid,
                     dif_rv_plic_irq_id_t irq_id) {
  if (devid == dt_pwrmgr_instance_id(kPwrmgrDt) &&
      irq_id == dt_pwrmgr_irq_to_plic_id(kPwrmgrDt, kDtPwrmgrIrqWakeup)) {
    CHECK_DIF_OK(dif_pwrmgr_irq_acknowledge(&pwrmgr, kDtPwrmgrIrqWakeup));
    return true;
  } else {
    return false;
  }
}

bool test_main(void) {
  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  CHECK_DIF_OK(dif_pwrmgr_init_from_dt(kPwrmgrDt, &pwrmgr));
  CHECK_DIF_OK(dif_rv_plic_init_from_dt(kRvPlicDt, &rv_plic));
  CHECK_DIF_OK(dif_sensor_ctrl_init_from_dt(kSensorCtrlDt, &sensor_ctrl));
  // Enable all the AON interrupts used in this test.
  dif_rv_plic_irq_id_t irq_id =
      dt_pwrmgr_irq_to_plic_id(kPwrmgrDt, kDtPwrmgrIrqWakeup);
  rv_plic_testutils_irq_range_enable(&rv_plic, kPlicTarget, irq_id, irq_id);
  // Enable pwrmgr interrupt
  CHECK_DIF_OK(dif_pwrmgr_irq_set_enabled(&pwrmgr, 0, kDifToggleEnabled));

  dif_pwrmgr_wakeup_reason_t wakeup_reason;
  CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_get(&pwrmgr, &wakeup_reason));

  if (wakeup_reason.request_sources == 0) {
    // This is a POR. Prepare to start the test.
    CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_clear(&pwrmgr));
    CHECK_DIF_OK(dif_pwrmgr_wakeup_request_recording_set_enabled(
        &pwrmgr, kDifToggleEnabled));
    // This enters deep sleep, so the clock control bits are irrelevant since
    // they are reset on wakeup.
    dif_pwrmgr_request_sources_t wakeup_sources;
    CHECK_DIF_OK(dif_pwrmgr_find_request_source(
        &pwrmgr, kDifPwrmgrReqTypeWakeup,
        dt_sensor_ctrl_instance_id(kSensorCtrlDt), kDtSensorCtrlWakeupWkupReq,
        &wakeup_sources));
    CHECK_STATUS_OK(
        pwrmgr_testutils_enable_low_power(&pwrmgr, wakeup_sources, 0));
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
