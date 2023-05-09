// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/ujson_ottf.h"

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/test_framework/ottf_console.h"
#include "sw/device/lib/ujson/ujson.h"

static status_t ottf_putbuf(void *io, const char *buf, size_t len) {
  const dif_uart_t *uart = (const dif_uart_t *)io;
  for (size_t i = 0; i < len; ++i) {
    TRY(dif_uart_byte_send_polled(uart, buf[i]));
  }
  return OK_STATUS((int32_t)len);
}

static status_t ottf_getc(void *io) {
  const dif_uart_t *uart = (const dif_uart_t *)io;
  uint8_t byte;
  TRY(dif_uart_byte_receive_polled(uart, &byte));
  TRY(ottf_console_flow_control(uart, kOttfConsoleFlowControlAuto));
  return OK_STATUS(byte);
}

ujson_t ujson_ottf_console(void) {
  return ujson_init(ottf_console_get(), ottf_getc, ottf_putbuf);
}
