// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_console.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

status_t ottf_flow_control_test(ujson_t *uj) {
  // Adjust the delay in the wait loop so that the host test harness
  // has enough time to starting sending data us on the UART.  Because
  // we aren't reading in the wait loop, we should get flow-control
  // event while in the wait loop.
  uint32_t delay = kDeviceType == kDeviceSimVerilator ? 1 : 500000;
  for (size_t i = 0; i < 10; ++i) {
    // Print a bunch of stuff so that ibex will be busy
    // driving the transmitter while the host sends data
    // to the UART.
    base_printf("WAIT\r\n");
    busy_spin_micros(delay);
  }

  base_printf("Reading\r\n");
  // Receive a line of text into a buffer.
  uint8_t buf[256] = {0};
  for (size_t i = 0; i < sizeof(buf) - 1; ++i) {
    char ch = (char)TRY(ujson_getc(uj));
    if (ch == '\n') {
      break;
    }
    buf[i] = ch;
  }

  // We'd better have gotten a flow control interrupt.
  CHECK(ottf_console_get_flow_control_irqs() > 0);

  // Print out the received data so the test can check that it matches what was
  // sent.
  base_printf("RESULT:%s\r\n", buf);
  return OK_STATUS();
}

bool test_main(void) {
  ujson_t uj = ujson_ottf_console();
  status_t status = ottf_flow_control_test(&uj);
  return status_ok(status);
}
