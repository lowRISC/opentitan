// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/sca_lib.h"

#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/testing/alert_handler_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static dif_rv_plic_t plic;
static dif_rstmgr_t rstmgr;
static dif_alert_handler_t alert_handler;
static dif_lc_ctrl_t lc;

sca_registered_alerts_t sca_get_triggered_alerts(void) {
  bool is_cause;

  sca_registered_alerts_t registered;
  registered.alerts_1 = 0;
  registered.alerts_2 = 0;
  registered.alerts_3 = 0;

  // Loop over all alert_cause regs
  for (size_t alert = 0; alert < ALERT_HANDLER_PARAM_N_ALERTS; alert++) {
    CHECK_DIF_OK(
        dif_alert_handler_alert_is_cause(&alert_handler, alert, &is_cause));
    if (is_cause) {
      if (alert < 32) {
        registered.alerts_1 |= (1 << alert);
      } else if (alert < 64) {
        registered.alerts_2 |= (1 << (alert - 32));
      } else {
        registered.alerts_3 |= (1 << (alert - 64));
      }
    }
  }

  // Loop over all alert_cause regs.
  for (dif_alert_handler_alert_t i = 0; i < ALERT_HANDLER_PARAM_N_ALERTS; i++) {
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(&alert_handler, i));
  }

  return registered;
}

void sca_configure_alert_handler(void) {
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  mmio_region_t base_addr =
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_plic_init(base_addr, &plic));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR);
  CHECK_DIF_OK(dif_alert_handler_init(base_addr, &alert_handler));

  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));

  dif_alert_handler_alert_t alerts[ALERT_HANDLER_PARAM_N_ALERTS];
  dif_alert_handler_class_t alert_classes[ALERT_HANDLER_PARAM_N_ALERTS];

  // Enable all incoming alerts and configure them to classa.
  for (dif_alert_handler_alert_t i = 0; i < ALERT_HANDLER_PARAM_N_ALERTS; ++i) {
    alerts[i] = i;
    alert_classes[i] = kDifAlertHandlerClassA;
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

  dif_alert_handler_class_config_t class_configs[] = {class_config};

  dif_alert_handler_class_t classes[] = {kDifAlertHandlerClassA};
  dif_alert_handler_config_t config = {
      .alerts = alerts,
      .alert_classes = alert_classes,
      .alerts_len = ARRAYSIZE(alerts),
      .classes = classes,
      .class_configs = class_configs,
      .classes_len = ARRAYSIZE(class_configs),
      .ping_timeout = 256,
  };

  CHECK_STATUS_OK(alert_handler_testutils_configure_all(&alert_handler, config,
                                                        kDifToggleEnabled));
  // Enables alert handler irq.
  CHECK_DIF_OK(dif_alert_handler_irq_set_enabled(
      &alert_handler, kDifAlertHandlerIrqClassa, kDifToggleEnabled));
}

status_t sca_read_device_id(ujson_t *uj) {
  mmio_region_t lc_reg = mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_BASE_ADDR);
  CHECK_DIF_OK(dif_lc_ctrl_init(lc_reg, &lc));

  dif_lc_ctrl_device_id_t lc_device_id;
  CHECK_DIF_OK(dif_lc_ctrl_get_device_id(&lc, &lc_device_id));

  // Send back to the host.
  penetrationtest_device_id_t uj_output;
  memcpy(uj_output.device_id, lc_device_id.data, 8 * sizeof(uint32_t));
  RESP_OK(ujson_serialize_penetrationtest_device_id_t, uj, &uj_output);

  return OK_STATUS();
}

void sca_configure_cpu(void) {
  uint32_t cpuctrl_csr;
  // Get current config.
  CSR_READ(CSR_REG_CPUCTRL, &cpuctrl_csr);
  // Disable the iCache.
  cpuctrl_csr = bitfield_field32_write(
      cpuctrl_csr, (bitfield_field32_t){.mask = 0x1, .index = 0}, 0);
  // Disable dummy instructions.
  cpuctrl_csr = bitfield_field32_write(
      cpuctrl_csr, (bitfield_field32_t){.mask = 0x1, .index = 2}, 0);
  // Write back config.
  CSR_WRITE(CSR_REG_CPUCTRL, cpuctrl_csr);
}
