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
#include "sw/device/lib/runtime/print.h"
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

// Function pointer to the currently active data sink.
static sink_func_ptr sink;
// Function pointer to a function that retrieves a single character.
static status_t (*getc)(void *);

// Staging buffer for the SPI console implementation.
static char spi_buf[kSpiDeviceMaxFramePayloadSizeBytes];
static size_t spi_buf_end;

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
      sink = get_uart_sink();
      getc = uart_getc;
      break;
    case (kOttfConsoleSpiDevice):
      ottf_console_configure_spi_device(&main_console, base_addr);
      sink = get_spi_device_sink();
      getc = spi_device_getc;
      spi_buf_end = 0;
      memset(spi_buf, 0, kSpiDeviceMaxFramePayloadSizeBytes);
      break;
    default:
      CHECK(false, "unsupported OTTF console interface.");
      break;
  }
}

status_t ottf_console_flushbuf(void *io) {
  size_t written_len = 0;
  if (kOttfTestConfig.console.putbuf_buffered && spi_buf_end > 0) {
    written_len = sink(io, spi_buf, spi_buf_end);
    if (spi_buf_end != written_len) {
      return DATA_LOSS((int32_t)(spi_buf_end - written_len));
    }
    spi_buf_end = 0;
  }
  return OK_STATUS((int32_t)written_len);
}

static status_t ottf_buffered_putbuf(void *io, const char *buf, size_t len) {
  if (len > sizeof(spi_buf)) {
    // Flush and skip the staging buffer if the payload is already the max size.
    TRY(ottf_console_flushbuf(io));
    size_t written_len = sink(io, buf, len);
    if (len != written_len) {
      return DATA_LOSS((int32_t)(len - written_len));
    }
  } else if ((spi_buf_end + len) <= sizeof(spi_buf)) {
    // There is room for the data in the staging buffer, copy it over.
    memcpy(&spi_buf[spi_buf_end], buf, len);
    spi_buf_end += len;
  } else {
    // The staging buffer is almost full; flush it before staging more data.
    TRY(ottf_console_flushbuf(io));
    memcpy(&spi_buf[spi_buf_end], buf, len);
    spi_buf_end += len;
  }
  return OK_STATUS((int32_t)len);
}

static status_t ottf_non_buffered_putbuf(void *io, const char *buf,
                                         size_t len) {
  size_t written_len = sink(io, buf, len);
  if (len != written_len) {
    return DATA_LOSS((int32_t)(len - written_len));
  }
  return OK_STATUS((int32_t)len);
}

status_t ottf_console_putbuf(void *io, const char *buf, size_t len) {
  if (kOttfTestConfig.console.putbuf_buffered) {
    return ottf_buffered_putbuf(io, buf, len);
  } else {
    return ottf_non_buffered_putbuf(io, buf, len);
  }
}

status_t ottf_console_getc(void *io) { return getc(io); }
