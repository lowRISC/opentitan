// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/ottf_console.h"

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/testing/test_framework/check.h"

#define MODULE_ID MAKE_MODULE_ID('o', 't', 'c')

// Main console.
static ottf_console_t main_console;

static volatile uint32_t flow_control_irqs;

ottf_console_t *ottf_console_get(void) { return &main_console; }

static status_t ottf_console_null_getc(void *io) {
  OT_DISCARD(io);
  return UNAVAILABLE();
}

static size_t ottf_console_null_sink(void *io, const char *buf, size_t len) {
  OT_DISCARD(io);
  OT_DISCARD(buf);
  return len;
}

void ottf_console_configure_null(ottf_console_t *console) {
  console->getc = ottf_console_null_getc;
  console->sink = ottf_console_null_sink;
}

void ottf_console_init(void) {
  // Initialize/Configure the console device.
  uintptr_t base_addr = kOttfTestConfig.console.base_addr;

  switch (kOttfTestConfig.console.type) {
#ifdef OTTF_CONSOLE_HAS_UART
    case kOttfConsoleUart:
      // Set a default for the console base address if the base address is not
      // configured. The default is to use UART0.
      if (base_addr == 0) {
        base_addr = dt_uart_primary_reg_block(kDtUart0);
      }

      ottf_console_configure_uart(&main_console, base_addr);
      // Initialize/Configure console flow control (if requested).
      if (kOttfTestConfig.enable_uart_flow_control) {
        ottf_console_uart_flow_control_enable(&main_console);
      }
      break;
#endif
#ifdef OTTF_CONSOLE_HAS_SPI_DEVICE
    case (kOttfConsoleSpiDevice):
      ottf_console_configure_spi_device(
          &main_console, base_addr, kOttfTestConfig.console_tx_indicator.enable,
          kOttfTestConfig.console_tx_indicator.spi_console_tx_ready_gpio,
          kOttfTestConfig.console_tx_indicator.spi_console_tx_ready_mio);
      // For the SPI console, we use the global SPI buffer.
      size_t main_spi_buf_sz;
      void *main_spi_buf =
          ottf_console_spi_get_main_staging_buffer(&main_spi_buf_sz);
      ottf_console_set_buffering(&main_console,
                                 kOttfTestConfig.console.putbuf_buffered,
                                 main_spi_buf, main_spi_buf_sz);
      break;
#endif
    default:
      // Create a null console.
      ottf_console_configure_null(&main_console);
      break;
  }

  base_set_stdout(ottf_console_get_buffer_sink(&main_console));
}

uint32_t ottf_console_get_flow_control_irqs(void) { return flow_control_irqs; }

bool ottf_console_flow_control_isr(uint32_t *exc_info) {
  flow_control_irqs += 1;
#ifdef OTTF_CONSOLE_HAS_UART
  return ottf_console_uart_flow_control_isr(exc_info, &main_console);
#else
  return false;
#endif
}

status_t ottf_console_flow_control(ottf_console_t *console,
                                   ottf_console_flow_control_t ctrl) {
#ifdef OTTF_CONSOLE_HAS_UART
  return ottf_console_uart_flow_control(console, ctrl);
#else
  return INVALID_ARGUMENT();
#endif
}

void ottf_console_set_buffering(ottf_console_t *console, bool enabled,
                                char *buffer, size_t size) {
  console->buffered = enabled;
  if (enabled) {
    console->buf = buffer;
    console->buf_size = size;
    memset(buffer, 0, size);
  } else {
    console->buf = NULL;
    console->buf_size = 0;
  }
  console->buf_end = 0;
}

status_t ottf_console_flush(ottf_console_t *console) {
  if (console->buffered && console->buf_end > 0) {
    size_t written_len = console->sink(console, console->buf, console->buf_end);
    size_t lost = console->buf_end - written_len;
    console->buf_end = 0;
    if (lost > 0) {
      return DATA_LOSS((int32_t)lost);
    } else {
      return OK_STATUS((int32_t)written_len);
    }
  }
  return OK_STATUS(0);
}

static status_t ottf_console_write_unbuffered(ottf_console_t *console,
                                              const char *buf, size_t len) {
  size_t written_len = console->sink(console, buf, len);
  if (written_len < len) {
    return DATA_LOSS((int32_t)(len - written_len));
  } else {
    return OK_STATUS((int32_t)written_len);
  }
}

static status_t ottf_console_write_buffered(ottf_console_t *console,
                                            const char *buf, size_t len) {
  if (len > console->buf_size) {
    // Flush and skip the staging buffer if the payload is already the max size.
    TRY(ottf_console_flush(console));
    return ottf_console_write_unbuffered(console, buf, len);
  } else if ((console->buf_end + len) <= console->buf_size) {
    // There is room for the data in the staging buffer, copy it over.
    memcpy(&console->buf[console->buf_end], buf, len);
    console->buf_end += len;
    return OK_STATUS((int32_t)len);
  } else {
    // The staging buffer is almost full; flush it before staging more data.
    TRY(ottf_console_flush(console));
    memcpy(&console->buf[console->buf_end], buf, len);
    console->buf_end += len;
    return OK_STATUS((int32_t)len);
  }
}

static status_t ottf_console_write(ottf_console_t *console, const char *buf,
                                   size_t len) {
  if (console->buffered) {
    return ottf_console_write_buffered(console, buf, len);
  } else {
    return ottf_console_write_unbuffered(console, buf, len);
  }
}

/**
 * Type-erased API for use with ujson.
 */

status_t ottf_console_flushbuf(void *io) {
  ottf_console_t *console = io;
  return ottf_console_flush(console);
}

status_t ottf_console_putbuf(void *io, const char *buf, size_t len) {
  ottf_console_t *console = io;
  return ottf_console_write(console, buf, len);
}

status_t ottf_console_getc(void *io) {
  ottf_console_t *console = io;
  return console->getc(io);
}

buffer_sink_t ottf_console_get_buffer_sink(ottf_console_t *console) {
  return (buffer_sink_t){.data = (void *)console, .sink = console->sink};
}
