// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_framework/test_main.h"
#include "sw/device/lib/testing/test_framework/test_status.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static dif_alert_handler_t alert_handler;
static dif_uart_t uart0;
static dif_rv_plic_t plic;

const test_config_t kTestConfig;

bool test_main(void) {
  CHECK_DIF_OK(dif_uart_init(
      mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR), &alert_handler));

  CHECK_DIF_OK(dif_uart_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &plic));

  CHECK_DIF_OK(dif_uart_init(
      mmio_region_from_addr(TOP_EARLGREY_UART0_BASE_ADDR), &uart0));

  // Generate the fatal fault.
  CHECK_DIF_OK(dif_uart_alert_force(&uart0, kDifUartAlertFatalFault));

  // Verify that alert handler received it.

  return true;
}
