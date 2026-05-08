// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_CONSOLE_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_CONSOLE_H_

#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_gpio.h"
#ifdef OTTF_CONSOLE_HAS_SPI_DEVICE
#include "sw/device/lib/testing/test_framework/ottf_console_spi.h"
#endif
#ifdef OTTF_CONSOLE_HAS_UART
#include "sw/device/lib/testing/test_framework/ottf_console_uart.h"
#endif
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/test_framework/ottf_console_types.h"

/**
 * OTTF console state.
 *
 * Typedef in ottf_console_types.h
 */
struct ottf_console {
  /** Console type. */
  ottf_console_type_t type;
  /* Function pointer to the currently active data sink. */
  sink_func_ptr sink;
  /* Function pointer to a function that retrieves a single character. */
  status_t (*getc)(void *);
  /* Enable SW buffering. */
  bool buffered;
  /** Staging buffer. */
  char *buf;
  /** Staging buffer size. */
  size_t buf_size;
  /** Where to write next to the staging buffer. */
  size_t buf_end;
  /** Auxiliary data, per console type */
  union {
#ifdef OTTF_CONSOLE_HAS_UART
    /** UART data. */
    ottf_console_uart_t uart;
#endif  // OTTF_CONSOLE_HAS_UART
#ifdef OTTF_CONSOLE_HAS_SPI_DEVICE
    /** SPI device data. */
    ottf_console_spi_t spi;
#endif  // OTTF_CONSOLE_HAS_SPI_DEVICE
  } data;
};

/**
 * Returns a pointer to the OTTF main console.
 */
ottf_console_t *ottf_console_get(void);

/**
 * Initializes the OTTF console device and connects to the printf buffer.
 */
void ottf_console_init(void);

/**
 * Configures software buffering of the console.
 *
 * If the console previously had buffering enabled, disabling buffering will
 * simply drop the content of the staging buffer. Therefore the content should
 * be flushed before disabling buffering.
 *
 * @param console Pointer to the console to configure
 * @param enabled Enable/disable buffering.
 * @param buffer Staging buffer used for buffering.
 * @param size Length of the staging buffer.
 */
void ottf_console_set_buffering(ottf_console_t *console, bool enabled,
                                char *buffer, size_t size);

/**
 * Manage flow control by inspecting the OTTF console device's receive FIFO.
 *
 * @param console A pointer to the console.
 * @param ctrl Set the next desired flow-control state.
 * @return The new state.
 */
status_t ottf_console_flow_control(ottf_console_t *console,
                                   ottf_console_flow_control_t ctrl);

/**
 * Manage console flow control *for the main console* from interrupt context.
 *
 * Call this when a console UART interrupt triggers.
 *
 * @param exc_info The OTTF execution info passed to all ISRs.
 * @return True if an RX Watermark IRQ was detected and handled. False
 * otherwise.
 */
bool ottf_console_flow_control_isr(uint32_t *exc_info);

/**
 * Returns the number of OTTF console flow control interrupts that have
 * occurred.
 */
uint32_t ottf_console_get_flow_control_irqs(void);

/**
 * Write a buffer to the OTTF console.
 *
 * @param io An IO context: pointer to an `ottf_console_t`.
 * @param buf The buffer to write to the OTTF console.
 * @param len The length of the buffer.
 * @return OK or an error.
 */
status_t ottf_console_putbuf(void *io, const char *buf, size_t len);

/**
 * Flush remaining buffered data to the OTTF console.
 *
 * On success, an OK_STATUS is returned with the number of flushed bytes.
 * On error, the unflushed data will be lost.
 *
 * @param io An IO context: pointer to an `ottf_console_t`.
 * @return OK or an error.
 */
status_t ottf_console_flushbuf(void *io);

/**
 * Get a single character from the OTTF console.
 *
 * @param io An IO context: pointer to an `ottf_console_t`.
 * @return The next character or an error.
 */
status_t ottf_console_getc(void *io);

/**
 * Get a buffer sink object for a console.
 *
 * This buffer sink can be used with `base_fprintf`.
 *
 * @param console Pointer to the console object.
 * @return A buffer sink.
 */
buffer_sink_t ottf_console_get_buffer_sink(ottf_console_t *console);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_CONSOLE_H_
