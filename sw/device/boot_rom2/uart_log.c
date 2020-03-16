// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0`

#include "sw/device/boot_rom2/uart_log.h"

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/print.h"
#include "sw/device/lib/runtime/hart.h"

/**
 * Handle for the 0th UART port.
 */
static dif_uart_t uart0;

dif_uart_t *uart_log_handle(void) { return &uart0; }

/**
 * Tries to write a buffer to the 0th UART. This function only exists to
 * drive logging, and should otherwise not be called directly.
 *
 * This function is called by error-handling code, and as such a failure
 * within it is treated asa double-fault.
 *
 * @param ignored a data pointer required by buf_sink_t, which is ignored.
 * @param buf a buffer to write to UART.
 * @param len the length of the buffer.
 * @return the number of bytes written, that is, the value of len.
 */
static size_t uart0_send_buf(void *ignored, const char *buf, size_t len) {
  size_t total_len = len;
  while (len > 0) {
    size_t bytes_written;
    bool success =
        dif_uart_bytes_send(&uart0, (const uint8_t *)buf, len, &bytes_written);
    if (!success) {
      // We have no way of logging this failure for now, since we're in the
      // middle of the UART stdout... which is used for logging. Oops.
      abort();
    }

    len -= bytes_written;
    buf += bytes_written;
  }
  return total_len;
}

void uart_log_init(void) {
  dif_uart_config_t config = {
      .baudrate = kUartBaudrate,
      .clk_freq_hz = kClockFreqHz,
      .parity_enable = kDifUartDisable,
      .parity = kDifUartParityEven,
  };

  mmio_region_t addr = mmio_region_from_addr(0x40000000);
  dif_uart_init(addr, &config, &uart0);

  base_set_stdout((buffer_sink_t){
      .sink = &uart0_send_buf,
  });
}
