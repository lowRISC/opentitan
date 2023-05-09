// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/alert_handler_testutils.h"
#include "sw/device/lib/testing/test_framework/FreeRTOSConfig.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "alert_handler_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/*
  In SV test, force the alert_handler's wait_cyc_mask_i input to shorten the
  ping request intervals. In C test, configure alert_handler to enable all
  alerts and local alerts. Then in SV test, wait until all alerts are pinged and
  check no alerts or local alert errors.
*/

OTTF_DEFINE_TEST_CONFIG();

static dif_alert_handler_t alert_handler;

static void alert_handler_config(void) {
  dif_alert_handler_alert_t alerts[ALERT_HANDLER_PARAM_N_ALERTS];
  dif_alert_handler_class_t alert_classes[ALERT_HANDLER_PARAM_N_ALERTS];

  // Enable all incoming alerts and configure them to classa.
  // This alert should never fire because we do not expect any incoming alerts.
  for (dif_alert_handler_alert_t i = 0; i < ALERT_HANDLER_PARAM_N_ALERTS; ++i) {
    alerts[i] = i;
    alert_classes[i] = kDifAlertHandlerClassA;
  }

  // Enable all local alerts and configure them to classb.
  dif_alert_handler_alert_t loc_alerts[ALERT_HANDLER_PARAM_N_LOC_ALERT];
  dif_alert_handler_class_t loc_alert_classes[ALERT_HANDLER_PARAM_N_LOC_ALERT];
  for (dif_alert_handler_alert_t i = 0; i < ALERT_HANDLER_PARAM_N_LOC_ALERT;
       ++i) {
    loc_alerts[i] = i;
    loc_alert_classes[i] = kDifAlertHandlerClassB;
  }

  dif_alert_handler_escalation_phase_t esc_phases[] = {
      {.phase = kDifAlertHandlerClassStatePhase0,
       .signal = 0,
       .duration_cycles = 2000}};

  dif_alert_handler_class_config_t class_config = {
      .auto_lock_accumulation_counter = kDifToggleDisabled,
      .accumulator_threshold = 0,
      .irq_deadline_cycles = 10000,
      .escalation_phases = esc_phases,
      .escalation_phases_len = ARRAYSIZE(esc_phases),
      .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase1,
  };

  dif_alert_handler_class_config_t class_configs[] = {class_config,
                                                      class_config};

  dif_alert_handler_class_t classes[] = {kDifAlertHandlerClassA,
                                         kDifAlertHandlerClassB};
  dif_alert_handler_config_t config = {
      .alerts = alerts,
      .alert_classes = alert_classes,
      .alerts_len = ARRAYSIZE(alerts),
      .local_alerts = loc_alerts,
      .local_alert_classes = loc_alert_classes,
      .local_alerts_len = ARRAYSIZE(loc_alerts),
      .classes = classes,
      .class_configs = class_configs,
      .classes_len = ARRAYSIZE(class_configs),
      .ping_timeout = 1000,
  };

  CHECK_STATUS_OK(alert_handler_testutils_configure_all(&alert_handler, config,
                                                        kDifToggleEnabled));
}

bool test_main(void) {
  CHECK_DIF_OK(dif_alert_handler_init(
      mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR),
      &alert_handler));

  alert_handler_config();
  return true;
}
