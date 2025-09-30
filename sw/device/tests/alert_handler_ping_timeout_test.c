// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <limits.h>
#include <stdbool.h>
#include <stdint.h>

#include "hw/top/dt/alert_handler.h"
#include "hw/top/dt/rv_plic.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/alert_handler_testutils.h"
#include "sw/device/lib/testing/test_framework/FreeRTOSConfig.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top/alert_handler_regs.h"  // Generated.

OTTF_DEFINE_TEST_CONFIG();

static dif_rv_plic_t plic;
static dif_alert_handler_t alert_handler;

enum {
  /**
   * PLIC target for the Ibex core.
   */
  kDtRvPlicTargetIbex0 = 0,
};

// Depends on the clock domain, sometimes alert handler will trigger a spurious
// alert after the alert timeout. (Issue #2321)
// So we allow class A interrupt to fire after the real timeout interrupt is
// triggered.
static volatile bool irq_fired = false;

/**
 * Initialize the peripherals used in this test.
 */
static void init_peripherals(void) {
  CHECK_DIF_OK(dif_rv_plic_init_from_dt(kDtRvPlic, &plic));
  CHECK_DIF_OK(dif_alert_handler_init_from_dt(kDtAlertHandler, &alert_handler));

  // Enable all the alert_handler interrupts used in this test.
  dt_plic_irq_id_t classa_irq = dt_alert_handler_irq_to_plic_id(
      kDtAlertHandler, kDtAlertHandlerIrqClassa);
  dt_plic_irq_id_t classb_irq = dt_alert_handler_irq_to_plic_id(
      kDtAlertHandler, kDtAlertHandlerIrqClassb);
  dt_plic_irq_id_t classc_irq = dt_alert_handler_irq_to_plic_id(
      kDtAlertHandler, kDtAlertHandlerIrqClassc);
  dt_plic_irq_id_t classd_irq = dt_alert_handler_irq_to_plic_id(
      kDtAlertHandler, kDtAlertHandlerIrqClassd);

  dt_plic_irq_id_t irq_ids[] = {classa_irq, classb_irq, classc_irq, classd_irq};
  for (size_t i = 0; i < ARRAYSIZE(irq_ids); ++i) {
    CHECK_DIF_OK(
        dif_rv_plic_irq_set_priority(&plic, irq_ids[i], /*priority=*/1u));
    CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(
        &plic, irq_ids[i], kDtRvPlicTargetIbex0, kDifToggleEnabled));
  }

  CHECK_DIF_OK(dif_rv_plic_target_set_threshold(&plic, kDtRvPlicTargetIbex0,
                                                /*threshold=*/0u));
}

/**
 * Program the alert handler to escalate on alerts upto phase 1 (i.e. wipe
 * secret) but not trigger reset. Then CPU can check if the correct interrupt
 * fires and check the local alert cause register.
 */
static void alert_handler_config(void) {
  // Enable all incoming alerts and configure them to class A.
  dif_alert_handler_alert_t alerts[ALERT_HANDLER_PARAM_N_ALERTS];
  dif_alert_handler_class_t alert_classes[ALERT_HANDLER_PARAM_N_ALERTS];
  for (dif_alert_handler_alert_t i = 0; i < ALERT_HANDLER_PARAM_N_ALERTS; ++i) {
    alerts[i] = i;
    alert_classes[i] = kDifAlertHandlerClassA;
  }

  // Enable alert ping fail local alert and configure that to classb.
  dif_alert_handler_local_alert_t loc_alerts[] = {
      kDifAlertHandlerLocalAlertAlertPingFail};
  dif_alert_handler_class_t loc_alert_classes[] = {kDifAlertHandlerClassB};

  dif_alert_handler_escalation_phase_t esc_phases[] = {
      {.phase = kDifAlertHandlerClassStatePhase0,
       .signal = UINT32_MAX,  // Take no action.
       .duration_cycles = 2000}};

  dif_alert_handler_class_config_t class_config = {
      .auto_lock_accumulation_counter = kDifToggleDisabled,
      .accumulator_threshold =
          1000,                  // Set to large number to defer escalation.
      .irq_deadline_cycles = 0,  // Disable IRQ timeouts.
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

  CHECK_STATUS_OK(alert_handler_testutils_configure_all(&alert_handler, config,
                                                        kDifToggleEnabled));
  // Enables alert handler irq.
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
bool ottf_handle_irq(uint32_t *exc_info, dt_instance_id_t inst_id,
                     dif_rv_plic_irq_id_t plic_irq_id) {
  // Check if this is the alert handler peripheral
  if (inst_id != dt_alert_handler_instance_id(kDtAlertHandler)) {
    return false;
  }

  // Convert PLIC IRQ ID to alert handler IRQ
  dt_alert_handler_irq_t irq =
      dt_alert_handler_irq_from_plic_id(kDtAlertHandler, plic_irq_id);

  // Acknowledge the interrupt
  CHECK_DIF_OK(dif_alert_handler_irq_acknowledge(&alert_handler, irq));

  // We expect Class B interrupt primarily, but may see Class A due to timing
  // (Issue #2321 - spurious alerts after timeout)
  if (irq == kDtAlertHandlerIrqClassb) {
    irq_fired = true;
    // Disable the interrupt after seeing the ping timeout
    CHECK_DIF_OK(dif_alert_handler_irq_set_enabled(
        &alert_handler, kDifAlertHandlerIrqClassb, kDifToggleDisabled));
  } else if (irq == kDtAlertHandlerIrqClassa) {
    // Allow Class A as per Issue #2321
    LOG_INFO("Received spurious Class A interrupt (expected per Issue #2321)");
  } else {
    CHECK(false, "Interrupt from unexpected class: %d", irq);
  }

  return true;
}

bool test_main(void) {
  init_peripherals();

  // Enable interrupts globally
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  alert_handler_config();

  // Wait for the ping timeout interrupt to fire
  ATOMIC_WAIT_FOR_INTERRUPT(irq_fired);

  // Check local alert cause.
  bool is_cause;
  dif_alert_handler_local_alert_t exp_local_alert =
      kDifAlertHandlerLocalAlertAlertPingFail;
  CHECK_DIF_OK(dif_alert_handler_local_alert_is_cause(
      &alert_handler, exp_local_alert, &is_cause));
  CHECK(is_cause, "Expect local alert cause: alert_ping_fail!");

  // Print out information about which alerts have been received.
  for (size_t id = 0; id < ALERT_HANDLER_PARAM_N_ALERTS; ++id) {
    bool is_cause;
    CHECK_DIF_OK(
        dif_alert_handler_alert_is_cause(&alert_handler, id, &is_cause));
    if (is_cause) {
      LOG_INFO("Received alert ID %u.", id);
    }
  }
  return true;
}
