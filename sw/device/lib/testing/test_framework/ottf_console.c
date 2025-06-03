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
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "spi_device_regs.h"  // Generated.

#define MODULE_ID MAKE_MODULE_ID('o', 't', 'c')

// Main console.
static ottf_console_t main_console;

static volatile uint32_t flow_control_irqs;

// Staging buffer for the SPI console implementation.
static char main_spi_buf[kSpiDeviceMaxFramePayloadSizeBytes];

ottf_console_t *ottf_console_get(void) { return &main_console; }

void ottf_console_init(void) {
  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &ottf_plic));
  // Initialize/Configure the console device.
  uintptr_t base_addr = kOttfTestConfig.console.base_addr;
  main_console.type = kOttfTestConfig.console.type;
  switch (kOttfTestConfig.console.type) {
    case kOttfConsoleUart:
      // Set a default for the console base address if the base address is not
      // configured. The default is to use UART0.
      if (base_addr == 0) {
        CHECK(kOttfTestConfig.console.type == kOttfConsoleUart);
        base_addr = TOP_EARLGREY_UART0_BASE_ADDR;
      }

      ottf_console_configure_uart(&main_console, base_addr);
      // Initialize/Configure console flow control (if requested).
      if (kOttfTestConfig.enable_uart_flow_control) {
        ottf_console_uart_flow_control_enable(&main_console);
      }
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

  base_set_stdout(ottf_console_get_buffer_sink(&main_console));
}

uint32_t ottf_console_get_flow_control_irqs(void) { return flow_control_irqs; }

bool ottf_console_flow_control_isr(uint32_t *exc_info) {
  flow_control_irqs += 1;
  return ottf_console_uart_flow_control_isr(exc_info, &main_console);
}

status_t ottf_console_flow_control(ottf_console_t *console,
                                   ottf_console_flow_control_t ctrl) {
  return ottf_console_uart_flow_control(console, ctrl);
}

void ottf_console_set_buffering(ottf_console_t *console, bool enabled,
                                char *buffer, size_t size) {
  console->buffered = enabled;
  if (enabled) {
    console->buf = buffer;
    console->buf_sz = size;
    console->buf_end = 0;
    memset(buffer, 0, size);
  } else {
    console->buf = NULL;
    console->buf_sz = 0;
    console->buf_end = 0;
  }
}

size_t ottf_console_flush(ottf_console_t *console) {
  size_t written_len = 0;
  if (console->buffered && console->buf_end > 0) {
    written_len = console->sink(console, console->buf, console->buf_end);
    size_t lost = console->buf_end - written_len;
    console->buf_end = 0;
    return lost;
  }
  return 0;
}

static size_t ottf_console_write_unbuffered(ottf_console_t *console,
                                            const char *buf, size_t len) {
  return console->sink(console, buf, len);
}

static size_t ottf_console_write_buffered(ottf_console_t *console,
                                          const char *buf, size_t len) {
  if (len > console->buf_sz) {
    // Flush and skip the staging buffer if the payload is already the max size.
    size_t lost = ottf_console_flush(console);
    if (lost > 0) {
      return 0;
    }
    return ottf_console_write_unbuffered(console, buf, len);
  } else if ((console->buf_end + len) <= console->buf_sz) {
    // There is room for the data in the staging buffer, copy it over.
    memcpy(&console->buf[console->buf_end], buf, len);
    console->buf_end += len;
    return len;
  } else {
    // The staging buffer is almost full; flush it before staging more data.
    size_t lost = ottf_console_flush(console);
    if (lost > 0) {
      return 0;
    }
    memcpy(&console->buf[console->buf_end], buf, len);
    console->buf_end += len;
    return len;
  }
}

static size_t ottf_console_write(ottf_console_t *console, const char *buf,
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
  size_t lost = ottf_console_flush(console);
  if (lost > 0) {
    return DATA_LOSS((int32_t)lost);
  }
  return OK_STATUS(0);
}

status_t ottf_console_putbuf(void *io, const char *buf, size_t len) {
  ottf_console_t *console = io;
  size_t written_len = ottf_console_write(console, buf, len);
  if (len != written_len) {
    return DATA_LOSS((int32_t)(len - written_len));
  }
  return OK_STATUS((int32_t)len);
}

status_t ottf_console_getc(void *io) {
  ottf_console_t *console = io;
  return console->getc(io);
}

buffer_sink_t ottf_console_get_buffer_sink(ottf_console_t *console) {
  return (buffer_sink_t){.data = (void *)console, .sink = console->sink};
}
