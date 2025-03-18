// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/testing/alert_handler_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"
#include "soc_proxy_regs.h"

OTTF_DEFINE_TEST_CONFIG();

static const dif_alert_handler_escalation_phase_t kEscProfiles[] = {
    {// Phase 0: non-maskable interrupt (NMI)
     .phase = kDifAlertHandlerClassStatePhase0,
     .signal = 0,
     .duration_cycles = 1000},
    {// Phase 1: life cycle scrap / lc_escalate_en
     .phase = kDifAlertHandlerClassStatePhase1,
     .signal = 1,
     .duration_cycles = 1000},
    {// Phase 2: reset
     .phase = kDifAlertHandlerClassStatePhase2,
     .signal = 3,
     .duration_cycles = 300}};

static const dif_alert_handler_class_config_t kConfigProfiles[] = {
    // Profile 0: Fatal alerts
    {
        // Lock accumulation counter as soon as escalation is triggered.
        .auto_lock_accumulation_counter = kDifToggleEnabled,
        // Trigger escalation on first event.
        .accumulator_threshold = 0,
        // Don't generate an IRQ.
        .irq_deadline_cycles = 0,
        // Escalation phases as defined above.
        .escalation_phases = kEscProfiles,
        .escalation_phases_len = 3,
        // Snapshot Alert Handler CSRs for crashdump in phase 1.
        .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase1,
    },
    // Profile 1: Recoverable alerts
    {
        // Lock accumulation counter as soon as escalation is triggered.
        .auto_lock_accumulation_counter = kDifToggleEnabled,
        // Delay escalation until more recoverable alerts than there are
        // externally are seen (so that this doesn't escalate within this test).
        .accumulator_threshold = 10000,
        // Don't generate an IRQ.
        .irq_deadline_cycles = 0,
        // Escalation phases as defined above.
        .escalation_phases = kEscProfiles,
        .escalation_phases_len = 3,
        // Snapshot Alert Handler CSRs for crashdump in phase 1.
        .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase1,
    },
};

bool test_main(void) {
  dif_alert_handler_t alert_handler;
  dif_rstmgr_t rstmgr;

  // Initialize DIF handles.
  CHECK_DIF_OK(dif_alert_handler_init(
      mmio_region_from_addr(TOP_DARJEELING_ALERT_HANDLER_BASE_ADDR),
      &alert_handler));
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_DARJEELING_RSTMGR_AON_BASE_ADDR), &rstmgr));

  // The first external alert is Fatal Alert External 0.
  const top_darjeeling_alert_id_t FIRST_SOC_PROXY_FATAL_ALERT_ID =
      kTopDarjeelingAlertIdSocProxyFatalAlertExternal0;
  // Keep this in sync with HW the last fatal external alert defined in
  // `soc_proxy.hjson`.
  const top_darjeeling_alert_id_t LAST_SOC_PROXY_FATAL_ALERT_ID =
      kTopDarjeelingAlertIdSocProxyFatalAlertExternal23;
  // The last external alert is a recoverable alert, and its ID is that of the
  // first external alert plus the number of alerts minus the one internal
  // alert.
  const top_darjeeling_alert_id_t LAST_SOC_PROXY_RECOV_ALERT_ID =
      FIRST_SOC_PROXY_FATAL_ALERT_ID + SOC_PROXY_PARAM_NUM_ALERTS - 1;

  // Read out previous alert crash dump (if it exists).
  bool alert_before_reset = false;
  top_darjeeling_alert_id_t previous_alert_id;
  size_t rstmgr_alert_info_size;
  CHECK_DIF_OK(
      dif_rstmgr_alert_info_get_size(&rstmgr, &rstmgr_alert_info_size));
  if (rstmgr_alert_info_size > 0) {
    dif_rstmgr_alert_info_dump_segment_t
        alert_info_dump[DIF_RSTMGR_ALERT_INFO_MAX_SIZE];
    size_t rstmgr_alert_info_dump_segments;
    CHECK_DIF_OK(dif_rstmgr_alert_info_dump_read(
        &rstmgr, alert_info_dump, rstmgr_alert_info_size,
        &rstmgr_alert_info_dump_segments));
    alert_handler_testutils_info_t alert_info;
    CHECK_STATUS_OK(alert_handler_testutils_info_parse(
        alert_info_dump, (int)rstmgr_alert_info_size, &alert_info));

    for (top_darjeeling_alert_id_t alert_id = FIRST_SOC_PROXY_FATAL_ALERT_ID;
         alert_id <= LAST_SOC_PROXY_FATAL_ALERT_ID; alert_id++) {
      if (alert_info.alert_cause[alert_id]) {
        LOG_INFO("Alert ID %0d registered before latest reset.", alert_id);
        alert_before_reset = true;
        previous_alert_id = alert_id;
      }
    }

    for (unsigned class = 0; class < ALERT_HANDLER_PARAM_N_CLASSES; class ++) {
      alert_handler_class_state_t state = alert_info.class_esc_state[class];
      if (state != kCstateIdle) {
        LOG_INFO("Alert class %0d: esc_state=%0d.", class, state);
      }
    }
  }

  // Configure Reset Manager to capture alert crash dumps.
  CHECK_DIF_OK(dif_rstmgr_alert_info_set_enabled(&rstmgr, kDifToggleEnabled));

  // Determine expected ID of alert: First all the fatal alerts, then all the
  // recoverable alerts.
  top_darjeeling_alert_id_t expected_alert_id;
  if (alert_before_reset) {
    expected_alert_id = previous_alert_id + 1;
  } else {
    expected_alert_id = FIRST_SOC_PROXY_FATAL_ALERT_ID;
  }

  // Loop over the remaining alerts.
  while (expected_alert_id <= LAST_SOC_PROXY_RECOV_ALERT_ID) {
    // Determine profile and configuration lock for alert, depending on whether
    // it's fatal or recoverable.
    dif_toggle_t locked;
    dif_alert_handler_class_config_t profile;
    if (expected_alert_id > LAST_SOC_PROXY_FATAL_ALERT_ID) {
      // Recoverable
      locked = kDifToggleDisabled;
      profile = kConfigProfiles[1];
    } else {
      // Fatal
      locked = kDifToggleEnabled;
      profile = kConfigProfiles[0];
    }

    // Set the alert we care about to class A.
    CHECK_DIF_OK(dif_alert_handler_configure_alert(
        &alert_handler, expected_alert_id, kDifAlertHandlerClassA,
        /*enabled=*/kDifToggleEnabled, /*locked=*/locked));

    // Configure class A.
    CHECK_DIF_OK(dif_alert_handler_configure_class(
        &alert_handler, kDifAlertHandlerClassA, profile,
        /*enabled=*/kDifToggleEnabled, /*locked=*/locked));

    LOG_INFO("Alert handler configured.");

    if (expected_alert_id > LAST_SOC_PROXY_FATAL_ALERT_ID) {
      // Recoverable alert: poll alert handler register to confirm alert.
      while (true) {
        bool is_cause;
        CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
            &alert_handler, expected_alert_id, &is_cause));
        if (is_cause) {
          break;
        }
        busy_spin_micros(5);
      }
      LOG_INFO("Alert ID %0d is cause.", expected_alert_id);
      CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(&alert_handler,
                                                       expected_alert_id));

      // Continue with the next recoverable alert.
      expected_alert_id++;
    } else {
      // Fatal alert: break loop, because a reset is expected before the next
      // fatal alert can be tested.
      break;
    }
  }

  // As far as SW is concerned, the test has passed when we reach this code, as
  // there are two scenarios:
  // a) Fatal alert: SW has just configured alert handler for a fatal alert.
  //    Until the fatal alert is triggered and the escalation led to a reset of
  //    the CPU, SW has no further tasks.  After the reset this function will be
  //    invoked again.
  // b) Recoverable alert: SW has looped over all recoverable alerts and has
  //    seen and acknowledged each of them.
  return true;
}
