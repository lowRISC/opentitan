// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/ottf_alerts.h"

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/alert_handler_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_alerts.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"

#if OPENTITAN_HAS_FLASH_CTRL
#include "hw/top/dt/flash_ctrl.h"
#endif  // OPENTITAN_HAS_FLASH_CTRL

static dif_alert_handler_t ottf_alert_handler;

status_t ottf_alerts_enable_all(void) {
  TRY(dif_alert_handler_init_from_dt(kDtAlertHandler, &ottf_alert_handler));

  size_t alert_count = kDtAlertCount;
  dif_alert_handler_alert_t alerts[alert_count];
  dif_alert_handler_class_t alert_classes[alert_count];

  for (dif_alert_handler_alert_t alert = 0, cfg_idx = 0;
       alert < ARRAYSIZE(alerts); alert++, cfg_idx++) {
#ifdef OPENTITAN_IS_EARLGREY
    // Temporarily skip alert 37 (`flash_ctrl_fatal_err`) on FPGAs and sims at
    // the owner stage since flash will not be provisioned with expected data.
    // See #23038.
    dt_alert_id_t fatal_err = dt_flash_ctrl_alert_to_alert_id(
        kDtFlashCtrl, kDtFlashCtrlAlertFatalErr);
    if (alert == fatal_err && kDeviceType != kDeviceSilicon) {
      cfg_idx--;
      alert_count--;
      continue;
    }
#endif

    alerts[cfg_idx] = alert;
    alert_classes[cfg_idx] = kDifAlertHandlerClassD;
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
      .alerts_len = alert_count,
      .classes = classes,
      .class_configs = class_configs,
      .classes_len = ARRAYSIZE(class_configs),
      .ping_timeout = UINT16_MAX,
  };
  TRY(alert_handler_testutils_configure_all(&ottf_alert_handler, config,
                                            kDifToggleDisabled));

  TRY(dif_alert_handler_irq_set_enabled(
      &ottf_alert_handler, kDifAlertHandlerIrqClassd, kDifToggleEnabled));

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

bool ottf_alerts_should_handle_irq(dt_instance_id_t devid,
                                   dif_rv_plic_irq_id_t plic_irq_id) {
  return kOttfTestConfig.catch_alerts &&
         devid == dt_alert_handler_instance_id(kDtAlertHandler) &&
         plic_irq_id == dt_alert_handler_irq_to_plic_id(
                            kDtAlertHandler, kDtAlertHandlerIrqClassd);
}

void ottf_alert_isr(uint32_t *exc_info) {
  dif_alert_handler_t alert_handler;
  CHECK_DIF_OK(dif_alert_handler_init_from_dt(kDtAlertHandler, &alert_handler));

  // Log all asserted alerts.
  for (dif_alert_handler_alert_t alert = 0; alert < kDtAlertCount; alert++) {
    bool is_cause = false;
    CHECK_DIF_OK(
        dif_alert_handler_alert_is_cause(&alert_handler, alert, &is_cause));
    if (is_cause) {
      LOG_ERROR("INFO: Alert %d is asserted", alert);
    }
  }

  abort();
}
