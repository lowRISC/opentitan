// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_console.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/uart_testutils.h"
#include "sw/device/lib/ujson/ujson.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/**
 * Test the ability to have several independent consoles. The main
 * console is connected to the "console" UART and a secondary console
 * is created which is connected to the "dut" UART.
 */

OTTF_DEFINE_TEST_CONFIG();

static dif_pinmux_t pinmux;
static ottf_console_t debug_console;

bool test_main(void) {
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  CHECK_STATUS_OK(uart_testutils_select_pinmux(&pinmux, /* uart= */ 1,
                                               kUartPinmuxChannelDut));
  ottf_console_configure_uart(&debug_console, TOP_EARLGREY_UART1_BASE_ADDR);
  LOG_INFO("Main UART console");
  base_fprintf(ottf_console_get_buffer_sink(&debug_console),
               "Second UART console\n");
  return true;
}
