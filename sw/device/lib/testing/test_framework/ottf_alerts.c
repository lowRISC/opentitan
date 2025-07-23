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
#include "sw/device/lib/testing/test_framework/check.h"

#include "alert_handler_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Maximum number of alerts that can be expected at once.
#define MAX_ALERTS_EXPECTED 16
// Number of words required to store all alerts one per bit.
#define ALERT_COUNT_WORDS (ALERT_HANDLER_PARAM_N_ALERTS + 31) / 32

static dif_alert_handler_t ottf_alert_handler;

status_t ottf_alerts_enable_all(void) {
  TRY(dif_alert_handler_init(
      mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR),
      &ottf_alert_handler));

  dif_alert_handler_alert_t alerts[ALERT_HANDLER_PARAM_N_ALERTS];
  dif_alert_handler_class_t alert_classes[ARRAYSIZE(alerts)];
  for (dif_alert_handler_alert_t i = 0; i < ARRAYSIZE(alerts); i++) {
    alerts[i] = i;
    alert_classes[i] = kDifAlertHandlerClassD;

    // Temporarily skip alert 37 (`flash_ctrl_fatal_err`) on FPGAs and sims at
    // the owner stage since flash will not be provisioned with expected data.
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
  TRY(alert_handler_testutils_configure_all(&ottf_alert_handler, config,
                                            kDifToggleDisabled));

  TRY(dif_alert_handler_irq_set_enabled(
      &ottf_alert_handler, kDifAlertHandlerIrqClassd, kDifToggleEnabled));

  dif_rv_plic_t rv_plic;
  TRY(dif_rv_plic_init(mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR),
                       &rv_plic));

  TRY(dif_rv_plic_irq_set_priority(&rv_plic,
                                   kTopEarlgreyPlicIrqIdAlertHandlerClassd,
                                   kDifRvPlicMaxPriority));
  TRY(dif_rv_plic_irq_set_enabled(
      &rv_plic, kTopEarlgreyPlicIrqIdAlertHandlerClassd,
      kTopEarlgreyPlicTargetIbex0, kDifToggleEnabled));
  TRY(dif_rv_plic_target_set_threshold(&rv_plic, kTopEarlgreyPlicTargetIbex0,
                                       kDifRvPlicMinPriority));

  irq_global_ctrl(true);
  irq_external_ctrl(true);

  return OK_STATUS();
}

status_t ottf_alerts_ignore_alert(dif_alert_handler_alert_t alert) {
  TRY(dif_alert_handler_configure_alert(
      &ottf_alert_handler, alert, kDifAlertHandlerClassD, kDifToggleDisabled,
      kDifToggleDisabled));

  return OK_STATUS();
}

static_assert(ALERT_HANDLER_PARAM_N_ALERTS < UINT8_MAX,
              "alert IDs stored as bytes with 0xff as sentinel");

// List of expected alerts and the number of elements in the list.
static volatile uint8_t alert_expected[MAX_ALERTS_EXPECTED] = {0};
static volatile size_t alert_expected_cnt = 0;

// Bitmap of whether each alert has been caught while expected.
static volatile uint32_t alert_caught[ALERT_COUNT_WORDS] = {0};

void ottf_alert_isr(uint32_t *exc_info) {
  OT_DISCARD(exc_info);

  bool expected_caught = false;

  // Iterate over expected alerts and check if they are currently asserted.
  //
  // Note: we don't want to iterate over all 65 alerts and check if they were
  // the cause because this is too slow for an ISR. Ibex has an instruction for
  // counting leading zeroes in `alert_expected` words so this should be faster.
  for (int i = 0; i < alert_expected_cnt; i++) {
    dif_alert_handler_alert_t alert =
        (dif_alert_handler_alert_t)alert_expected[i];

    bool is_cause = false;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(&ottf_alert_handler, alert,
                                                  &is_cause));

    if (is_cause) {
      CHECK_DIF_OK(
          dif_alert_handler_alert_acknowledge(&ottf_alert_handler, alert));
      alert_caught[alert / 32] |= (1 << (alert % 32));
      expected_caught = true;
    }
  }

  if (!expected_caught) {
    // Log all asserted alerts.
    // We can pay the cost of iterating all alerts in the failure case.
    for (dif_alert_handler_alert_t alert = 0;
         alert < ALERT_HANDLER_PARAM_N_ALERTS; alert++) {
      bool is_cause = false;
      CHECK_DIF_OK(dif_alert_handler_alert_is_cause(&ottf_alert_handler, alert,
                                                    &is_cause));

      // Don't print expected alerts that were triggered at the same time as
      // unexpected alerts (unlikely but possible).
      bool cause_expected = false;
      for (int i = 0; i < alert_expected_cnt; i++) {
        if (alert_expected[i] == alert) {
          cause_expected = true;
          break;
        }
      }

      if (is_cause && !cause_expected) {
        LOG_ERROR("ERROR: Alert %d is asserted but not expected", alert);
      }
    }

    test_status_set(kTestStatusFailed);
    abort();
  }

  // Clear the alert escalation counter.
  CHECK_DIF_OK(dif_alert_handler_escalation_clear(&ottf_alert_handler,
                                                  kDifAlertHandlerClassD));
  // Complete the IRQ at the alert handler.
  CHECK_DIF_OK(dif_alert_handler_irq_acknowledge(&ottf_alert_handler,
                                                 kDifAlertHandlerIrqClassd));
}

status_t ottf_alerts_expect_alert_start(dif_alert_handler_alert_t alert) {
  if (alert < 0 || alert > kTopEarlgreyAlertIdLast) {
    return INVALID_ARGUMENT();
  }

  // Check for a full list.
  if (alert_expected_cnt >= MAX_ALERTS_EXPECTED) {
    return RESOURCE_EXHAUSTED();
  }

  alert_expected[alert_expected_cnt] = (uint8_t)alert;
  alert_expected_cnt++;

  return OK_STATUS();
}

status_t ottf_alerts_expect_alert_finish(dif_alert_handler_alert_t alert) {
  if (alert < 0 || alert > kTopEarlgreyAlertIdLast) {
    return INVALID_ARGUMENT();
  }
  // Find the index of this alert in the `alert_expected` list.
  int expected_idx = 0;
  for (; expected_idx < alert_expected_cnt; expected_idx++) {
    if (alert_expected[expected_idx] == alert) {
      break;
    }
  }

  if (alert_expected_cnt == 0 || expected_idx >= alert_expected_cnt) {
    // This alert was not expected with `ottf_alerts_expect_alert_start`.
    return FAILED_PRECONDITION();
  }

  // Shift the list down one space to clear this expectation.
  if (alert_expected_cnt < MAX_ALERTS_EXPECTED) {
    for (int i = expected_idx + 1; i < alert_expected_cnt; i++) {
      alert_expected[i - 1] = alert_expected[i];
    }
  }
  alert_expected_cnt--;

  uint32_t alert_word_idx = alert / 32;
  uint32_t alert_bit_idx = alert % 32;

  if (((alert_caught[alert_word_idx] >> alert_bit_idx) & 1) == 0) {
    // Alert was not caught when expected.
    return NOT_FOUND();
  }

  // Forget that the alert was caught.
  alert_caught[alert_word_idx] &= ~(1 << alert_bit_idx);

  return OK_STATUS();
}
