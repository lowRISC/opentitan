// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/ottf_alerts.h"

#include "sw/device/lib/arch/boot_stage.h"
#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/testing/alert_handler_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"

status_t ottf_alerts_enable_all(void) {
  TRY(dif_alert_handler_init_from_dt(kDtAlertHandler, &ottf_alert_handler));

  dif_alert_handler_alert_t alerts[kDtAlertCount];
  dif_alert_handler_class_t alert_classes[ARRAYSIZE(alerts)];
  for (dif_alert_handler_alert_t i = 0; i < ARRAYSIZE(alerts); i++) {
    alerts[i] = i;
    alert_classes[i] = kDifAlertHandlerClassD;

    // Temporarily skip alert 37 (`flash_ctrl_fatal_err`) on FPGAs and sims at
    // the owner stage since flash will not be provisioned with expected data.
    // See #23038.
    if (i == kTopEarlgreyAlertIdFlashCtrlFatalErr &&
        kDeviceType != kDeviceSilicon) {
      alerts[i] = 0;
    }
  }

  dif_alert_handler_escalation_phase_t esc_phases[] = {
      {.phase = kDifAlertHandlerClassStatePhase0,
       .signal = 0,
       .duration_cycles = 2000}};
  dif_alert_handler_class_config_t class_config = {
      .auto_lock_accumulation_counter = kDifToggleDisabled,
      .accumulator_threshold = UINT16_MAX,
      .irq_deadline_cycles = UINT32_MAX,
      .escalation_phases = esc_phases,
      .escalation_phases_len = ARRAYSIZE(esc_phases),
      .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase1,
  };
  dif_alert_handler_class_config_t class_configs[] = {class_config};
  dif_alert_handler_class_t classes[] = {kDifAlertHandlerClassD};

  dif_alert_handler_config_t config = {
      .alerts = alerts,
      .alert_classes = alert_classes,
      .alerts_len = ARRAYSIZE(alerts),
      .classes = classes,
      .class_configs = class_configs,
      .classes_len = ARRAYSIZE(class_configs),
      .ping_timeout = UINT16_MAX,
  };
  TRY(alert_handler_testutils_configure_all(&alert_handler, config,
                                            kDifToggleDisabled));

  TRY(dif_alert_handler_irq_set_enabled(
      &alert_handler, kDifAlertHandlerIrqClassd, kDifToggleEnabled));

  dif_rv_plic_t rv_plic;
  TRY(dif_rv_plic_init_from_dt(kDtRvPlic, &rv_plic));

  dt_plic_irq_id_t classd_plic_id = dt_alert_handler_irq_to_plic_id(
      kDtAlertHandler, kDtAlertHandlerIrqClassd);

  TRY(dif_rv_plic_irq_set_priority(&rv_plic, classd_plic_id,
                                   kDifRvPlicMaxPriority));
  TRY(dif_rv_plic_irq_set_enabled(&rv_plic, classd_plic_id, 0,
                                  kDifToggleEnabled));
  TRY(dif_rv_plic_target_set_threshold(&rv_plic, 0, kDifRvPlicMinPriority));

  irq_global_ctrl(true);
  irq_external_ctrl(true);

  return OK_STATUS();
}
