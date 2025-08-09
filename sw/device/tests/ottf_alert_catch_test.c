// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "dt/dt_uart.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

OTTF_DEFINE_TEST_CONFIG(.enable_concurrency = false);

// This test forces an alert and expects OTTF to catch and report it.
bool test_main(void) {
  dif_uart_t uart;
  CHECK_DIF_OK(dif_uart_init_from_dt(kDtUart0, &uart));

  LOG_INFO("Forcing alert");
  CHECK_DIF_OK(dif_uart_alert_force(&uart, kDifUartAlertFatalFault));

  LOG_INFO("Waiting for alert to be caught");
  busy_spin_micros(1000);

  LOG_INFO("Alert was not caught, we should not have gotten here");
  return true;
}
