// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_alerts.h"
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

enum {
  kAlertTimeoutMicros = 1000,
};

bool test_main(void) {
  dif_uart_t uart1, uart2, uart3;
  CHECK_DIF_OK(dif_uart_init(
      mmio_region_from_addr(TOP_EARLGREY_UART1_BASE_ADDR), &uart1));
  CHECK_DIF_OK(dif_uart_init(
      mmio_region_from_addr(TOP_EARLGREY_UART2_BASE_ADDR), &uart2));
  CHECK_DIF_OK(dif_uart_init(
      mmio_region_from_addr(TOP_EARLGREY_UART3_BASE_ADDR), &uart3));

  LOG_INFO("Forcing alert on UART1 (expected)");
  CHECK_STATUS_OK(
      ottf_alerts_expect_alert_start(kTopEarlgreyAlertIdUart1FatalFault));
  CHECK_DIF_OK(dif_uart_alert_force(&uart1, kDifUartAlertFatalFault));
  busy_spin_micros(kAlertTimeoutMicros);
  CHECK_STATUS_OK(
      ottf_alerts_expect_alert_finish(kTopEarlgreyAlertIdUart1FatalFault));

  LOG_INFO("Forcing alert on UART2 (ignored)");
  CHECK_STATUS_OK(ottf_alerts_ignore_alert(kTopEarlgreyAlertIdUart2FatalFault));
  CHECK_DIF_OK(dif_uart_alert_force(&uart2, kDifUartAlertFatalFault));
  busy_spin_micros(kAlertTimeoutMicros);

  LOG_INFO("Forcing alert on UART3 (unexpected)");
  CHECK_DIF_OK(dif_uart_alert_force(&uart3, kDifUartAlertFatalFault));

  LOG_INFO("Waiting for alert to be caught");
  busy_spin_micros(kAlertTimeoutMicros);

  LOG_INFO("Alert was not caught, we should not have gotten here");
  return false;
}
