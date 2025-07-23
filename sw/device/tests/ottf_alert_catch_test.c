// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// This test exercises OTTF's alert catching mechanism.
//
// We force two alerts: `Uart1FatalFault` and `Uart2FatalFault`. We expect the
// first to be handled by our custom handler and the second to be handled by
// OTTF leading to an error message and abort.
//
// The test is considered passing if we abort with `Alert 2 is asserted` and
// failing if the test ends naturally.

OTTF_DEFINE_TEST_CONFIG();

volatile bool uart1_alert_fired = false;
enum {
  kAlertTimeoutMicros = 1000,
};

// Handle UART1's fatal fault alert, ignore all others.
bool ottf_alert_isr(uint32_t *exc_info) {
  (void)exc_info;

  dif_alert_handler_t alert_handler;
  CHECK_DIF_OK(dif_alert_handler_init(
      mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR),
      &alert_handler));

  bool is_cause = false;
  CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
      &alert_handler, kTopEarlgreyAlertIdUart1FatalFault, &is_cause));
  uart1_alert_fired = is_cause;

  if (uart1_alert_fired) {
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, kTopEarlgreyAlertIdUart1FatalFault));
  }

  return uart1_alert_fired;
}

bool test_main(void) {
  dif_uart_t uart1, uart2;
  CHECK_DIF_OK(dif_uart_init(
      mmio_region_from_addr(TOP_EARLGREY_UART1_BASE_ADDR), &uart1));
  CHECK_DIF_OK(dif_uart_init(
      mmio_region_from_addr(TOP_EARLGREY_UART2_BASE_ADDR), &uart2));

  LOG_INFO("Forcing alert on UART1 (should be handled)");
  CHECK_DIF_OK(dif_uart_alert_force(&uart1, kDifUartAlertFatalFault));

  LOG_INFO("Waiting for UART1 alert to be caught");
  ibex_timeout_t timeout = ibex_timeout_init(kAlertTimeoutMicros);
  while (!uart1_alert_fired) {
    CHECK(!ibex_timeout_check(&timeout), "UART1 alert not caught");
  }

  LOG_INFO("Forcing alert on UART2 (should cause abort)");
  CHECK_DIF_OK(dif_uart_alert_force(&uart2, kDifUartAlertFatalFault));

  LOG_INFO("Waiting for alert to be caught");
  busy_spin_micros(kAlertTimeoutMicros);

  LOG_INFO("Alert was not caught, we should not have gotten here");
  return false;
}
