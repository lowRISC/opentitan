// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/ottf_console.h"

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/testing/spi_device_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_console_internal.h"
#include "sw/device/lib/testing/test_framework/ottf_isrs.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"

// TODO: make this toplevel agnostic.
#include "dt/dt_rv_plic.h"
#include "dt/dt_uart.h"

#include "spi_device_regs.h"  // Generated.

#define MODULE_ID MAKE_MODULE_ID('o', 't', 'c')

// Potential DIF handles for OTTF console communication.
dif_gpio_t ottf_console_gpio;
dif_pinmux_t ottf_console_pinmux;

// Main console.
static ottf_console_t main_console;

// Staging buffer for the SPI console implementation.
static char main_spi_buf[kSpiDeviceMaxFramePayloadSizeBytes];

ottf_console_t *ottf_console_get(void) { return &main_console; }

void ottf_console_init(void) {
  // Initialize/Configure the console device.
  uintptr_t base_addr = kOttfTestConfig.console.base_addr;

  switch (kOttfTestConfig.console.type) {
    case kOttfConsoleUart:
      // Set a default for the console base address if the base address is not
      // configured. The default is to use UART0.
      if (base_addr == 0) {
        CHECK(kOttfTestConfig.console.type == kOttfConsoleUart);
        base_addr = dt_uart_primary_reg_block(kDtUart0);
      }

      ottf_console_configure_uart(&main_console, base_addr);
      break;
    case (kOttfConsoleSpiDevice):
      ottf_console_configure_spi_device(
          &main_console, base_addr, kOttfTestConfig.console_tx_indicator.enable,
          kOttfTestConfig.console_tx_indicator.spi_console_tx_ready_gpio,
          kOttfTestConfig.console_tx_indicator.spi_console_tx_ready_mio);
      // For the SPI console, we use the global SPI buffer.
      ottf_console_set_buffering(&main_console,
                                 kOttfTestConfig.console.putbuf_buffered,
                                 main_spi_buf, sizeof(main_spi_buf));
      break;
    default:
      CHECK(false, "unsupported OTTF console interface.");
      break;
  }

  base_set_stdout((buffer_sink_t){.data = (void *)&main_console,
                                  .sink = main_console.sink});
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
