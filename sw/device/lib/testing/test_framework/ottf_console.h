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
 * Returns a pointer to the main OTTF console.
 */
ottf_console_t *ottf_console_get(void);

/**
 * Set the main console.
 *
 * The main console is the one used by the ujson console by default
 * and by base_printf.
 *
 * @param console Pointer to the console.
 */

void ottf_console_set_main(ottf_console_t *console);

/**
 * Initializes the OTTF main console device according to the
 * test settings, and connects it to the printf buffer.
 *
 * Also initialize some global variables which are necessary
 * for the OTTF console subsystem to work.
 */
void ottf_console_init(void);

/**
 * Configures the given OTTF console.
 *
 * If `base_addr` is set to 0, the default peripheral for the
 * type will be used.
 *
 * @param console Pointer to the console to setup.
 * @param type Console type.
 * @param base_addr Pointer to the peripheral's base address.
 */
void ottf_console_setup(ottf_console_t *console, ottf_console_type_t type,
                        uintptr_t base_addr);

/**
 * Configure OTTF SPI TX GPIO indicator of a console.
 *
 * @param console Pointer to the console to configure
 * @param enable Enable/Disable indicator.
 * @param gpio The GPIO to use to signal to the host that the SPI console buffer
 * is not empty.
 * @param mio The MIO to connect to the GPIO pin above
 */
void ottf_console_spi_setup_tx_indicator(ottf_console_t *console, bool enable,
                                         uint32_t gpio, uint32_t mio);

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
 * @param console Pointer to the console to configure
 * @param ctrl Set the next desired flow-control state.
 * @return The new state.
 */
status_t ottf_console_flow_control(ottf_console_t *console,
                                   ottf_console_flow_control_t ctrl);

/**
 * Enable flow control for a console.
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
void ottf_console_flow_control_enable(ottf_console_t *console);

/**
 * Manage console flow control *for the main console* from interrupt context.
 *
 * Call this when a console UART interrupt triggers. If you want to manage
 * control flow for non-main consoles, use `ottf_console_uart_flow_control_isr`.
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
 * @return True if an RX Watermark IRQ was detected and handled. False
 * otherwise.
 */
bool ottf_console_uart_flow_control_isr(ottf_console_t *console);

/**
 * Returns the number of OTTF console flow control interrupts that have
 * occurred.
 */
uint32_t ottf_console_get_flow_control_irqs(void);

/**
 * TODO
 */
size_t ottf_console_write(ottf_console_t *console, const char *buf, size_t len);

/**
 * Read data from the host via the OTTF SPI device console into a provided
 * buffer.
 *
 * The function waits for spi upload commands, then transfers data in chunks
 * until a transmission complete signal is received. If the size of data sent
 * from the host is greater than the provided buffer, then the excess data will
 * be discarded.
 *
 * @param console Console to use, must of SPI device type.
 * @param buf_size The size, in bytes, of the `buf`.
 * @param[out] buf A pointer to the location where the data should be stored.
 * @return The number of bytes actually received from the host.
 */
size_t ottf_console_spi_device_read(ottf_console_t *console, size_t buf_size,
                                    uint8_t *const buf);

/**
 * Write a buffer to the OTTF console.
 *
 * @param io An IO context: pointer to an `ottf_console_t`
 * @param buf The buffer to write to the OTTF console.
 * @param len The length of the buffer.
 * @return OK or an error.
 */
status_t ottf_console_putbuf(void *io, const char *buf, size_t len);

/**
 * Flush remaining buffered data to the OTTF console.
 *
 * @param io An IO context: pointer to an `ottf_console_t`
 * @return OK or an error.
 */
status_t ottf_console_flushbuf(void *io);

/**
 * Get a single character from the OTTF console.
 *
 * @param io An IO context: pointer to an `ottf_console_t`
 * @return The next character or an error.
 */
status_t ottf_console_getc(void *io);

/**
 * TODO
 */
buffer_sink_t ottf_console_buffer_sink(ottf_console_t *console);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_CONSOLE_H_
