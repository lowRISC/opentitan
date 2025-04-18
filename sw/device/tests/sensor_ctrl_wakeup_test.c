// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_sensor_ctrl.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "sensor_ctrl_regs.h"  // Generated.

OTTF_DEFINE_TEST_CONFIG();

static const dt_pwrmgr_t kPwrmgrDt = 0;
static_assert(kDtPwrmgrCount == 1, "this test expects a pwrmgr");
static const dt_rv_plic_t kRvPlicDt = 0;
static_assert(kDtRvPlicCount == 1, "this test expects exactly one rv_plic");
static const dt_sensor_ctrl_t kSensorCtrlDt = 0;
static_assert(kDtSensorCtrlCount == 1,
              "this test expects exactly one sensor_ctrl");

enum {
  kPlicTarget = 0,
};

static dif_pwrmgr_t pwrmgr;
static dif_rv_plic_t plic;

static bool get_wakeup_status(void) {
  dif_pwrmgr_request_sources_t wake_req = ~0u;
  CHECK_DIF_OK(dif_pwrmgr_get_current_request_sources(
      &pwrmgr, kDifPwrmgrReqTypeWakeup, &wake_req));
  return (wake_req > 0);
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
  dif_sensor_ctrl_t sensor_ctrl;

  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  // Initialize the PLIC.
  CHECK_DIF_OK(dif_rv_plic_init_from_dt(kRvPlicDt, &plic));

  // Initialize pwrmgr
  CHECK_DIF_OK(dif_pwrmgr_init_from_dt(kPwrmgrDt, &pwrmgr));

  // Initialize sensor_ctrl
  CHECK_DIF_OK(dif_sensor_ctrl_init_from_dt(kSensorCtrlDt, &sensor_ctrl));

  // Enable all the AON interrupts used in this test.
  dif_rv_plic_irq_id_t plic_id =
      dt_pwrmgr_irq_to_plic_id(kPwrmgrDt, kDtPwrmgrIrqWakeup);
  rv_plic_testutils_irq_range_enable(&plic, kPlicTarget, plic_id, plic_id);

  // Enable pwrmgr interrupt
  CHECK_DIF_OK(dif_pwrmgr_irq_set_enabled(&pwrmgr, 0, kDifToggleEnabled));

  // Capture the number of events to test
  uint32_t sensor_ctrl_events = SENSOR_CTRL_PARAM_NUM_ALERT_EVENTS;

  dif_pwrmgr_domain_config_t sleep_config =
      kDifPwrmgrDomainOptionMainPowerInLowPower;

  // Clear any prior events before we start the test
  for (size_t i = 0; i < sensor_ctrl_events; ++i) {
    CHECK_DIF_OK(dif_sensor_ctrl_clear_recov_event(&sensor_ctrl, i));
  }

  for (size_t i = 0; i < sensor_ctrl_events; ++i) {
    LOG_INFO("Testing sensor_ctrl event %d", i);

    // Enable the alert on the sensor_ctrl side
    CHECK_DIF_OK(
        dif_sensor_ctrl_set_alert_en(&sensor_ctrl, i, kDifToggleEnabled));

    // Setup event trigger
    CHECK_DIF_OK(dif_sensor_ctrl_set_ast_event_trigger(&sensor_ctrl, i,
                                                       kDifToggleEnabled));

    // Normal sleep.
    dif_pwrmgr_request_sources_t wakeup_sources;
    CHECK_DIF_OK(dif_pwrmgr_find_request_source(
        &pwrmgr, kDifPwrmgrReqTypeWakeup,
        dt_sensor_ctrl_instance_id(kSensorCtrlDt), kDtSensorCtrlWakeupWkupReq,
        &wakeup_sources));
    CHECK_STATUS_OK(pwrmgr_testutils_enable_low_power(&pwrmgr, wakeup_sources,
                                                      sleep_config));

    // Enter low power mode.
    LOG_INFO("Issue WFI to enter sleep");
    wait_for_interrupt();

    // Wakeup from sleep.
    LOG_INFO("Wake from sleep");

    dif_sensor_ctrl_events_t events;
    CHECK_DIF_OK(dif_sensor_ctrl_get_recov_events(&sensor_ctrl, &events));

    if (events != (1 << i)) {
      LOG_ERROR("Recoverable event 0x%x does not match expectation %d", events,
                i);
    }

    // Disable the alert on the sensor_ctrl side
    CHECK_DIF_OK(
        dif_sensor_ctrl_set_alert_en(&sensor_ctrl, i, kDifToggleDisabled));

    // clear event trigger
    CHECK_DIF_OK(dif_sensor_ctrl_set_ast_event_trigger(&sensor_ctrl, i,
                                                       kDifToggleDisabled));

    // since there is synchronization delay to trigger clearing and actual event
    // de-assertion, clear and poll until it is finished before moving on
    while (events) {
      CHECK_DIF_OK(dif_sensor_ctrl_clear_recov_event(&sensor_ctrl, i));
      CHECK_DIF_OK(dif_sensor_ctrl_get_recov_events(&sensor_ctrl, &events));
    }

    // ensure the de-asserted events have cleared from the wakeup pipeline
    // within 30us
    IBEX_SPIN_FOR(!get_wakeup_status(), 30);
  }

  return true;
}
