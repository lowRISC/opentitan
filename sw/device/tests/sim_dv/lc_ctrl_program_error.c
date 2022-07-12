// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/alert_handler_testutils.h"
#include "sw/device/lib/testing/lc_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/FreeRTOSConfig.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/*
 TO BE FILLED IN
 */

OTTF_DEFINE_TEST_CONFIG();

static dif_alert_handler_t alert_handler;
static dif_lc_ctrl_t lc_ctrl;
static dif_rstmgr_t rstmgr;

static const dif_alert_handler_escalation_phase_t kEscProfiles[] = {
    // TODO:
    // this duration must be long enough to
    // accommodate a few jtag transactions
    // how can this be done in a non-hardcoded way?
    {.phase = kDifAlertHandlerClassStatePhase0,
     .signal = 1,
     .duration_cycles = 10000},
    {.phase = kDifAlertHandlerClassStatePhase1,
     .signal = 3,
     .duration_cycles = 10000}};

static const dif_alert_handler_class_config_t kConfigProfiles[] = {{
    .auto_lock_accumulation_counter = kDifToggleDisabled,
    .accumulator_threshold = 0,
    .irq_deadline_cycles = 0,
    .escalation_phases = kEscProfiles,
    .escalation_phases_len = 2,
    .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase0,
}};

bool test_main(void) {
  CHECK_DIF_OK(dif_lc_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_BASE_ADDR), &lc_ctrl));

  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));

  CHECK_DIF_OK(dif_alert_handler_init(
      mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR),
      &alert_handler));

  // Check if there was a HW reset caused by the escalation.
  dif_rstmgr_reset_info_bitfield_t rst_info;
  CHECK_DIF_OK(dif_rstmgr_reset_info_get(&rstmgr, &rst_info));
  CHECK_DIF_OK(dif_rstmgr_reset_info_clear(&rstmgr));

  if (rst_info & kDifRstmgrResetInfoPor) {
    // set the alert we care about to class A
    CHECK_DIF_OK(dif_alert_handler_configure_alert(
        &alert_handler, kTopEarlgreyAlertIdLcCtrlFatalProgError,
        kDifAlertHandlerClassA, /*enabled=*/kDifToggleEnabled,
        /*locked=*/kDifToggleEnabled));

    // configurate class A
    CHECK_DIF_OK(dif_alert_handler_configure_class(
        &alert_handler, kDifAlertHandlerClassA, kConfigProfiles[0],
        /*enabled=*/kDifToggleEnabled,
        /*locked=*/kDifToggleEnabled));

    // Initiate transition into scrap
    dif_lc_ctrl_token_t zero_token = {0, 0, 0, 0, 0, 0, 0, 0,
                                      0, 0, 0, 0, 0, 0, 0, 0};

    // DV sync message
    LOG_INFO("Begin life cycle transition");

    // Mutex acquire should always succeed, there are no competing agents
    CHECK_DIF_OK(dif_lc_ctrl_mutex_try_acquire(&lc_ctrl));
    CHECK_DIF_OK(dif_lc_ctrl_configure(&lc_ctrl, kDifLcCtrlStateScrap, false,
                                       &zero_token));
    CHECK_DIF_OK(dif_lc_ctrl_transition(&lc_ctrl));

    // halt execution
    wait_for_interrupt();

  } else if (rst_info & kDifRstmgrResetInfoEscalation) {
    LOG_INFO("Reset due to alert escalation");
    return true;
  } else {
    LOG_FATAL("unexpected reset info %d", rst_info);
  }

  return false;
}
