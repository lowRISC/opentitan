// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/runtime/print_uart.h"

#include <stdarg.h>
// #include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

// #include "sw/device/lib/base/macros.h"
// #include "sw/device/lib/base/memory.h"
// #include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_uart.h"

static size_t base_dev_uart(void *data, const char *buf, size_t len) {
  const dif_uart_t *uart = (const dif_uart_t *)data;
  for (size_t i = 0; i < len; ++i) {
    if (dif_uart_byte_send_polled(uart, (uint8_t)buf[i]) != kDifOk) {
      return i;
    }
  }
  return len;
}

sink_func_ptr get_uart_sink(void) { return &base_dev_uart; }

void base_uart_stdout(const dif_uart_t *uart) {
  base_set_stdout(
      (buffer_sink_t){.data = (void *)uart, .sink = &base_dev_uart});
}
