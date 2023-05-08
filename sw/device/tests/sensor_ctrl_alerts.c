// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_sensor_ctrl.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/nv_counter_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rand_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "sensor_ctrl_regs.h"  // Generated.

OTTF_DEFINE_TEST_CONFIG();

/**
 * This test checks that incoming ast events can be
 * configured as both recoverable and fatal.
 * Further, this test checks that recoverable and fatal
 * events are able to reach their proper alert_handler
 * destination.
 *
 * Since fatal events do not stop firing once asserted,
 * this test performs a self reset after every fatal
 * event.  In order to keep track of how far the test
 * has advanced, a non-volatile counter in flash is
 * used to track current progress.
 */
static dif_rstmgr_t rstmgr;
static dif_flash_ctrl_state_t flash_ctrl;
static dif_sensor_ctrl_t sensor_ctrl;
static dif_alert_handler_t alert_handler;

/**
 *  Clear event trigger and recoverable status.
 */
static void clear_event(uint32_t idx, dif_toggle_t fatal) {
  CHECK_DIF_OK(dif_sensor_ctrl_set_ast_event_trigger(&sensor_ctrl, idx,
                                                     kDifToggleDisabled));

  if (!dif_toggle_to_bool(fatal)) {
    CHECK_DIF_OK(dif_sensor_ctrl_clear_recov_event(&sensor_ctrl, idx));
  }
}

static uint32_t get_events(dif_toggle_t fatal) {
  dif_sensor_ctrl_events_t events = 0;
  if (dif_toggle_to_bool(fatal)) {
    CHECK_DIF_OK(dif_sensor_ctrl_get_fatal_events(&sensor_ctrl, &events));
  } else {
    CHECK_DIF_OK(dif_sensor_ctrl_get_recov_events(&sensor_ctrl, &events));
  }
  return events;
}

/**
 *  Check alert cause registers are correctly set
 */
static void check_alert_state(dif_toggle_t fatal) {
  bool fatal_cause = false;
  bool recov_cause = false;

  CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
      &alert_handler, kTopEarlgreyAlertIdSensorCtrlFatalAlert, &fatal_cause));

  CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
      &alert_handler, kTopEarlgreyAlertIdSensorCtrlRecovAlert, &recov_cause));

  if (dif_toggle_to_bool(fatal)) {
    CHECK(fatal_cause & !recov_cause,
          "Fatal alert not correctly observed in alert handler");
  } else {
    CHECK(recov_cause & !fatal_cause,
          "Recov alert not correctly observed in alert handler");
  }

  CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
      &alert_handler, kTopEarlgreyAlertIdSensorCtrlRecovAlert));
  CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
      &alert_handler, kTopEarlgreyAlertIdSensorCtrlFatalAlert));
};

/**
 *  First configure fatality of the desired event.
 *  Then trigger the event from sensor_ctrl to ast.
 *  Next poll for setting of correct events inside sensor_ctrl status.
 *  When a recoverable event is triggerd, make sure only recoverable
 *  status is seen, likewise for fatal events.
 *  Finally, check for correct capture of cause in alert handler.
 */
static void test_event(uint32_t idx, dif_toggle_t fatal) {
  // Configure event fatality
  CHECK_DIF_OK(dif_sensor_ctrl_set_alert_fatal(&sensor_ctrl, idx, fatal));

  // Trigger event
  CHECK_DIF_OK(dif_sensor_ctrl_set_ast_event_trigger(&sensor_ctrl, idx,
                                                     kDifToggleEnabled));

  // wait for events to set
  IBEX_SPIN_FOR(get_events(fatal) > 0, 1);

  // Check for the event in ast sensor_ctrl
  // if the event is not set, error
  CHECK(((get_events(fatal) >> idx) & 0x1) == 1, "Event %d not observed in AST",
        idx);

  // check the opposite fatality setting, should not be set
  CHECK(((get_events(!fatal) >> idx) & 0x1) == 0,
        "Event %d observed in AST when it should not be", idx);

  // clear event trigger
  clear_event(idx, fatal);

  // check whether alert handler captured the event
  check_alert_state(fatal);
};

enum {
  // Counter for event index.
  kCounterEventIdx,
  // Counter for number of events tested.
  kCounterNumTests,
  // Max number of events to test per run.
  kNumTestsMax = SENSOR_CTRL_PARAM_NUM_ALERT_EVENTS >> 1,
};

static uint32_t get_next_event_to_test(void) {
  uint32_t event_idx;
  // Reseed so that we don't see the same sequence after each reset.
  rand_testutils_reseed();
  do {
    CHECK_STATUS_OK(
        flash_ctrl_testutils_counter_get(kCounterEventIdx, &event_idx));
    CHECK_STATUS_OK(
        flash_ctrl_testutils_counter_increment(&flash_ctrl, kCounterEventIdx));
    // Drop each event randomly to reduce run time.
  } while (rand_testutils_gen32() <= UINT32_MAX >> 1 &&
           event_idx < SENSOR_CTRL_PARAM_NUM_ALERT_EVENTS);
  return event_idx;
}

bool test_main(void) {
  // Initialize flash_ctrl
  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash_ctrl,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));

  // Initialize sensor_ctrl
  CHECK_DIF_OK(dif_sensor_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SENSOR_CTRL_BASE_ADDR), &sensor_ctrl));

  // Initialize alert_handler
  CHECK_DIF_OK(dif_alert_handler_init(
      mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR),
      &alert_handler));

  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));

  // Enable both recoverable and fatal alerts
  CHECK_DIF_OK(dif_alert_handler_configure_alert(
      &alert_handler, kTopEarlgreyAlertIdSensorCtrlRecovAlert,
      kDifAlertHandlerClassA, kDifToggleEnabled, kDifToggleEnabled));
  CHECK_DIF_OK(dif_alert_handler_configure_alert(
      &alert_handler, kTopEarlgreyAlertIdSensorCtrlFatalAlert,
      kDifAlertHandlerClassA, kDifToggleEnabled, kDifToggleEnabled));

  // Enable flash access
  CHECK_STATUS_OK(
      flash_ctrl_testutils_default_region_access(&flash_ctrl,
                                                 /*rd_en*/ true,
                                                 /*prog_en*/ true,
                                                 /*erase_en*/ true,
                                                 /*scramble_en*/ false,
                                                 /*ecc_en*/ false,
                                                 /*he_en*/ false));

  // Make sure we do not try to test more than half of all available events
  // in a single test.  Testing too many would just make the run time too
  // long.
  uint32_t value = 0;
  CHECK_STATUS_OK(flash_ctrl_testutils_counter_get(kCounterNumTests, &value));
  uint32_t event_idx = get_next_event_to_test();
  if (event_idx == SENSOR_CTRL_PARAM_NUM_ALERT_EVENTS ||
      value >= kNumTestsMax) {
    LOG_INFO("Tested all events");
    return true;
  } else {
    LOG_INFO("Testing event %d", event_idx);
  }

  // test recoverable event
  test_event(event_idx, /*fatal*/ kDifToggleDisabled);

  // test fatal event
  test_event(event_idx, /*fatal*/ kDifToggleEnabled);

  // increment flash counter to know where we are
  CHECK_STATUS_OK(
      flash_ctrl_testutils_counter_increment(&flash_ctrl, kCounterNumTests));

  // Now request system to reset and test again
  LOG_INFO("Rebooting system");
  CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));
  wait_for_interrupt();

  return false;
}
