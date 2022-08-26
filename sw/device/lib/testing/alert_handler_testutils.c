// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/math.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/testing/test_framework/check.h"

#include "alert_handler_regs.h"  // Generated

void alert_handler_testutils_configure_all(
    const dif_alert_handler_t *alert_handler, dif_alert_handler_config_t config,
    dif_toggle_t locked) {
  CHECK(alert_handler != NULL);
  CHECK(dif_is_valid_toggle(locked));

  // Check lengths of alert, local alert, and class arrays.
  CHECK((config.alerts_len > 0 && config.alerts != NULL &&
         config.alert_classes != NULL) ||
        (config.alerts_len == 0 && config.alerts == NULL &&
         config.alert_classes == NULL));
  CHECK((config.local_alerts_len > 0 && config.local_alerts != NULL &&
         config.local_alert_classes != NULL) ||
        (config.local_alerts_len == 0 && config.local_alerts == NULL &&
         config.local_alert_classes == NULL));
  CHECK((config.classes_len > 0 && config.classes != NULL &&
         config.class_configs != NULL) ||
        (config.classes_len == 0 && config.classes == NULL &&
         config.class_configs == NULL));

  // Check that the provided ping timeout actually fits in the timeout
  // register, which is smaller than a native word length.
  CHECK(config.ping_timeout <=
        ALERT_HANDLER_PING_TIMEOUT_CYC_SHADOWED_PING_TIMEOUT_CYC_SHADOWED_MASK);

  // Configure and enable the requested alerts.
  for (int i = 0; i < config.alerts_len; ++i) {
    CHECK_DIF_OK(dif_alert_handler_configure_alert(
        alert_handler, config.alerts[i], config.alert_classes[i],
        kDifToggleEnabled, locked));
  }

  // Configure and enable the requested local alerts.
  for (int i = 0; i < config.local_alerts_len; ++i) {
    CHECK_DIF_OK(dif_alert_handler_configure_local_alert(
        alert_handler, config.local_alerts[i], config.local_alert_classes[i],
        kDifToggleEnabled, locked));
  }

  // Configure and enable the requested classes.
  for (int i = 0; i < config.classes_len; ++i) {
    CHECK_DIF_OK(dif_alert_handler_configure_class(
        alert_handler, config.classes[i], config.class_configs[i],
        kDifToggleEnabled, locked));
  }

  // Configure the ping timer.
  CHECK_DIF_OK(dif_alert_handler_configure_ping_timer(
      alert_handler, config.ping_timeout, kDifToggleEnabled, locked));
}

uint32_t alert_handler_testutils_get_cycles_from_us(uint64_t microseconds) {
  uint64_t cycles = udiv64_slow(microseconds * kClockFreqPeripheralHz, 1000000,
                                /*rem_out=*/NULL);
  CHECK(cycles < UINT32_MAX,
        "The value 0x%08x%08x can't fit into the 32 bits timer counter.",
        (cycles >> 32), (uint32_t)cycles);
  return (uint32_t)cycles;
}
