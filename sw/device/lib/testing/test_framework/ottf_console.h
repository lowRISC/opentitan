// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_CONSOLE_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_CONSOLE_H_

#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"

/**
 * Flow control state.
 */
typedef enum ottf_console_flow_control {
  /** No flow control enabled. */
  kOttfConsoleFlowControlNone = 0,
  /** Automatically determine the next flow control state. */
  kOttfConsoleFlowControlAuto = 1,
  /**
   * Flow control is in the `Resume` state (safe to receive).
   * This is also the ASCII code for `XON`.
   */
  kOttfConsoleFlowControlResume = 17,
  /**
   * Flow control is in the `Pause` state (risk of overrun).
   * This is also the ASCII code for `XOFF`.
   */
  kOttfConsoleFlowControlPause = 19,
} ottf_console_flow_control_t;

/**
 * OTTF console state.
 */
typedef struct ottf_console {
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
  size_t buf_sz;
  /** Where to write next to the staging buffer. */
  size_t buf_end;
  /** Auxiliary data, per console type */
  union {
    /** UART data. */
    struct {
      /** DIF handle. */
      dif_uart_t dif;
      // This variable is shared between the interrupt service handler and user
      // code.
      volatile ottf_console_flow_control_t flow_control_state;
    } uart;
    /** SPI device data. */
    struct {
      /** DIF handle. */
      dif_spi_device_handle_t dif;
      /** SPI device frame number. */
      uint32_t frame_num;
      /** TX ready GPIO, set to kOttfSpiNoTxGpio if not used. */
      dif_gpio_pin_t tx_ready_gpio;
    } spi;
  } data;
} ottf_console_t;

/**
 * Returns a pointer to the OTTF console device DIF handle.
 */
ottf_console_t *ottf_console_get(void);

/**
 * Initializes the OTTF console device and connects to the printf buffer.
 */
void ottf_console_init(void);

/**
 * Configures the given UART to be used by the OTTF console.
 *
 * @param console Console pointer
 * @param base_addr The base address of the UART to use.
 */
void ottf_console_configure_uart(ottf_console_t *console, uintptr_t base_addr);

/**
 * Configures the given SPI device to be used by the OTTF console.
 *
 * @param console Console pointer
 * @param base_addr The base address of the SPI device to use.
 * @param tx_ready_enable Enable TX indicator
 * @param tx_ready_gpio If TX indicator is enable, GPIO number to use.
 * @param tx_ready_mio If TX indicator is enable, MIO number to which to connect
 * it.
 */
void ottf_console_configure_spi_device(ottf_console_t *console,
                                       uintptr_t base_addr,
                                       bool tx_ready_enable,
                                       uint32_t tx_ready_gpio,
                                       uint32_t tx_ready_mio);

/**
 * Configures software buffering of the console.
 *
 * If the console previously had buffering enabled, disabling buffering will
 * simply drop the content of the staging buffer. Therefore the content should
 * be flushed before disabling buffering.
 *
 * @param console Pointer to the console to configure
 * @param enable Enable/Disable buffering.
 * @param buffer Staging buffer used for buffering.
 * @param size Length of the staging buffer.
 */
void ottf_console_set_buffering(ottf_console_t *console, bool enabled,
                                char *buffer, size_t size);

/**
 * Manage flow control by inspecting the OTTF console device's receive FIFO.
 *
 * @param uart A Pointer to the console.
 * @param ctrl Set the next desired flow-control state.
 * @return The new state.
 */
status_t ottf_console_flow_control(ottf_console_t *console,
                                   ottf_console_flow_control_t ctrl);

/**
 * Enable flow control for the OTTF console.
 *
 * Enables flow control on the UART associated with the OTTF console. Flow
 * control is managed by enabling the RX watermark IRQ and sending a `Pause`
 * (aka XOFF) when the RX FIFO depth reaches 16 bytes.  A `Resume` (aka XON) is
 * sent when the RX FIFO has been drained to 4 bytes.
 *
 * This function configures UART interrupts at the PLIC and enables interrupts
 * at the CPU.
 *
 * WARNING Control requires IRQ dispatching. The main console will automatically
 * dispatch control IRQs on calls to `ottf_console_flow_control_isr`. If you
 * want to dispatch control flow IRQs for non-main console, you must call
 * manually call `ottf_console_uart_flow_control_isr` on the console from your
 * IRQ handler.
 *
 * @param console Pointer to the console.
 */
void ottf_console_uart_flow_control_enable(ottf_console_t *console);

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
 * Manage console flow control from interrupt context.
 *
 * You should only call this function directly for *non-main* consoles.
 *
 * @param exc_info The OTTF execution info passed to all ISRs.
 * @param console Pointer to the console.
 * @return True if an RX Watermark IRQ was detected and handled. False
 * otherwise.
 */
bool ottf_console_uart_flow_control_isr(uint32_t *exc_info,
                                        ottf_console_t *console);

/**
 * Returns the number of OTTF console flow control interrupts that have
 * occurred.
 */
uint32_t ottf_console_get_flow_control_irqs(void);

/**
 * Read data from the host via the OTTF SPI device console into a provided
 * buffer.
 *
 * The function waits for spi upload commands, then transfers data in chunks
 * until a transmission complete signal is received. If the size of data sent
 * from the host is greater than the provided buffer, then the excess data will
 * be discarded.
 *
 * @param buf_size The size, in bytes, of the `buf`.
 * @param[out] buf A pointer to the location where the data should be stored.
 * @return The number of bytes actually received from the host.
 */
size_t ottf_console_spi_device_read(ottf_console_t *console, size_t buf_size,
                                    uint8_t *const buf);

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
