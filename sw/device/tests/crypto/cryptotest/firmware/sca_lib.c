// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/testing/alert_handler_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static const uint32_t kPlicTarget = kTopEarlgreyPlicTargetIbex0;
static dif_rv_plic_t plic;
static dif_rstmgr_t rstmgr;
static dif_alert_handler_t alert_handler;

#define NUM_ALERTS 31

// Manually select alerts we are interested in.
dif_alert_handler_alert_t alerts[NUM_ALERTS] = {
    kTopEarlgreyAlertIdSramCtrlRetAonFatalError,
    kTopEarlgreyAlertIdFlashCtrlRecovErr,
    kTopEarlgreyAlertIdFlashCtrlFatalStdErr,
    kTopEarlgreyAlertIdFlashCtrlFatalErr,
    kTopEarlgreyAlertIdFlashCtrlFatalPrimFlashAlert,
    kTopEarlgreyAlertIdFlashCtrlRecovPrimFlashAlert,
    kTopEarlgreyAlertIdRvDmFatalFault,
    kTopEarlgreyAlertIdRvPlicFatalFault,
    kTopEarlgreyAlertIdAesRecovCtrlUpdateErr,
    kTopEarlgreyAlertIdAesFatalFault,
    kTopEarlgreyAlertIdHmacFatalFault,
    kTopEarlgreyAlertIdKmacRecovOperationErr,
    kTopEarlgreyAlertIdKmacFatalFaultErr,
    kTopEarlgreyAlertIdOtbnFatal,
    kTopEarlgreyAlertIdOtbnRecov,
    kTopEarlgreyAlertIdKeymgrRecovOperationErr,
    kTopEarlgreyAlertIdKeymgrFatalFaultErr,
    kTopEarlgreyAlertIdCsrngRecovAlert,
    kTopEarlgreyAlertIdCsrngFatalAlert,
    kTopEarlgreyAlertIdEntropySrcRecovAlert,
    kTopEarlgreyAlertIdEntropySrcFatalAlert,
    kTopEarlgreyAlertIdEdn0RecovAlert,
    kTopEarlgreyAlertIdEdn0FatalAlert,
    kTopEarlgreyAlertIdEdn1RecovAlert,
    kTopEarlgreyAlertIdEdn1FatalAlert,
    kTopEarlgreyAlertIdSramCtrlMainFatalError,
    kTopEarlgreyAlertIdRomCtrlFatal,
    kTopEarlgreyAlertIdRvCoreIbexFatalSwErr,
    kTopEarlgreyAlertIdRvCoreIbexRecovSwErr,
    kTopEarlgreyAlertIdRvCoreIbexFatalHwErr,
    kTopEarlgreyAlertIdRvCoreIbexRecovHwErr};

/**
 * Returns the registered alerts.
 *
 * Checks which of the picked alerts are registered by the alert handler. If
 * the alert was registered, set a bit mask and clear the alert register.
 */
uint32_t sca_get_triggered_alerts(void) {
  uint32_t reg_alerts = 0;

  for (size_t it = 0; it < NUM_ALERTS; it++) {
    bool is_cause;
    dif_alert_handler_alert_t is_alert = alerts[it];
    CHECK_DIF_OK(
        dif_alert_handler_alert_is_cause(&alert_handler, is_alert, &is_cause));
    if (is_cause) {
      CHECK_DIF_OK(
          dif_alert_handler_alert_acknowledge(&alert_handler, is_alert));
      reg_alerts |= (1 << it);
    }
  }

  return reg_alerts;
}

/**
 * Configures the alert handler for FI.
 *
 * Register the alerts we are interested in and let them escalate to Phase0
 * only.
 *
 */
void sca_configure_alert_handler(void) {
  mmio_region_t base_addr =
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_rstmgr_init(base_addr, &rstmgr));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_plic_init(base_addr, &plic));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR);
  CHECK_DIF_OK(dif_alert_handler_init(base_addr, &alert_handler));

  rv_plic_testutils_irq_range_enable(&plic, kPlicTarget,
                                     kTopEarlgreyPlicIrqIdAlertHandlerClassa,
                                     kTopEarlgreyPlicIrqIdAlertHandlerClassd);

  // Map all alerts to AlertHandlerClassA.
  dif_alert_handler_class_t alert_classes[NUM_ALERTS];
  for (size_t it = 0; it < NUM_ALERTS; it++) {
    alert_classes[it] = kDifAlertHandlerClassA;
  }

  // Only escalate to phase 0, no reset should occur.
  dif_alert_handler_escalation_phase_t esc_phases[] = {
      {.phase = kDifAlertHandlerClassStatePhase0,
       .signal = 0,
       .duration_cycles = 10000}};

  // Configure alert handler.
  dif_alert_handler_class_config_t class_config[] = {{
      .auto_lock_accumulation_counter = kDifToggleDisabled,
      .accumulator_threshold = 0,
      .irq_deadline_cycles = 10000,
      .escalation_phases = esc_phases,
      .escalation_phases_len = ARRAYSIZE(esc_phases),
      .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase1,
  }};

  dif_alert_handler_class_t classes[] = {kDifAlertHandlerClassA};
  dif_alert_handler_config_t config = {
      .alerts = alerts,
      .alert_classes = alert_classes,
      .alerts_len = ARRAYSIZE(alerts),
      .classes = classes,
      .class_configs = class_config,
      .classes_len = ARRAYSIZE(class_config),
      .ping_timeout = 0,
  };

  CHECK_STATUS_OK(alert_handler_testutils_configure_all(&alert_handler, config,
                                                        kDifToggleEnabled));
}

/**
 * Configures Ibex for SCA and FI.
 *
 * This function disables the iCache and the dummy instructions using the
 * CPU Control and Status Register (cpuctrlsts).
 *
 */
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
