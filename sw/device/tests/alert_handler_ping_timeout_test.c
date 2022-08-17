// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <limits.h>
#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/alert_handler_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/FreeRTOSConfig.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "alert_handler_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "sw/device/lib/testing/autogen/isr_testutils.h"

OTTF_DEFINE_TEST_CONFIG();

static dif_rv_plic_t plic;
static dif_alert_handler_t alert_handler;
static const uint32_t kPlicTarget = kTopEarlgreyPlicTargetIbex0;

static plic_isr_ctx_t plic_ctx = {
    .rv_plic = &plic,
    .hart_id = kPlicTarget,
};

// Depends on the clock domain, sometimes alert handler will trigger a spurious
// alert after the alert timeout. (Issue #2321)
// So we allow class A interrupt to fire after the real timeout interrupt is
// triggered.
static alert_handler_isr_ctx_t alert_handler_ctx = {
    .alert_handler = &alert_handler,
    .plic_alert_handler_start_irq_id = kTopEarlgreyPlicIrqIdAlertHandlerClassa,
    .expected_irq = kDifAlertHandlerIrqClassb,
    .is_only_irq = false,
};

/**
 * Initialize the peripherals used in this test.
 */
static void init_peripherals(void) {
  mmio_region_t base_addr =
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_plic_init(base_addr, &plic));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR);
  CHECK_DIF_OK(dif_alert_handler_init(base_addr, &alert_handler));

  // Enable all the alert_handler interrupts used in this test.
  rv_plic_testutils_irq_range_enable(&plic, kPlicTarget,
                                     kTopEarlgreyPlicIrqIdAlertHandlerClassa,
                                     kTopEarlgreyPlicIrqIdAlertHandlerClassd);
}

/**
 * Program the alert handler to escalate on alerts upto phase 1 (i.e. wipe
 * secret) but not trigger reset. Then CPU can check if the correct interrupt
 * fires and check the local alert cause register.
 */
static void alert_handler_config(void) {
  dif_alert_handler_alert_t alerts[ALERT_HANDLER_PARAM_N_ALERTS];
  dif_alert_handler_class_t alert_classes[ALERT_HANDLER_PARAM_N_ALERTS];

  // Enable all incoming alerts and configure them to classa.
  // This alert should never fire because we do not expect any incoming alerts.
  for (int i = 0; i < ALERT_HANDLER_PARAM_N_ALERTS; ++i) {
    alerts[i] = i;
    alert_classes[i] = kDifAlertHandlerClassA;
  }

  // Enable alert ping fail local alert and configure that to classb.
  dif_alert_handler_local_alert_t loc_alerts[] = {
      kDifAlertHandlerLocalAlertAlertPingFail};
  dif_alert_handler_class_t loc_alert_classes[] = {kDifAlertHandlerClassB};

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
      .ping_timeout = 1,
  };

  alert_handler_testutils_configure_all(&alert_handler, config,
                                        kDifToggleEnabled);
  // Enables alert handler irq.
  CHECK_DIF_OK(dif_alert_handler_irq_set_enabled(
      &alert_handler, kDifAlertHandlerIrqClassa, kDifToggleEnabled));

  CHECK_DIF_OK(dif_alert_handler_irq_set_enabled(
      &alert_handler, kDifAlertHandlerIrqClassb, kDifToggleEnabled));
}

/**
 * External ISR.
 *
 * Handles all peripheral interrupts on Ibex. PLIC asserts an external interrupt
 * line to the CPU, which results in a call to this OTTF ISR. This ISR
 * overrides the default OTTF implementation.
 */
void ottf_external_isr(void) {
  top_earlgrey_plic_peripheral_t peripheral_serviced;
  dif_alert_handler_irq_t irq_serviced;
  isr_testutils_alert_handler_isr(plic_ctx, alert_handler_ctx,
                                  &peripheral_serviced, &irq_serviced);
  CHECK(peripheral_serviced == kTopEarlgreyPlicPeripheralAlertHandler,
        "Interurpt from unexpected peripheral: %d", peripheral_serviced);
}

bool test_main(void) {
  init_peripherals();

  alert_handler_config();

  // Enable the external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  wait_for_interrupt();

  // Check local alert cause.
  bool is_cause;
  dif_alert_handler_local_alert_t exp_local_alert =
      kDifAlertHandlerLocalAlertAlertPingFail;
  CHECK_DIF_OK(dif_alert_handler_local_alert_is_cause(
      &alert_handler, exp_local_alert, &is_cause));
  CHECK(is_cause, "Expect local alert cause: alert_ping_fail!");

  return true;
}
