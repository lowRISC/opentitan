// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_CONSOLE_UART_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_CONSOLE_UART_H_

#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/testing/test_framework/ottf_console_types.h"

typedef struct ottf_console_uart {
  // DIF handle.
  dif_uart_t dif;
  // This variable is shared between the interrupt service handler and user
  // code.
  volatile ottf_console_flow_control_t flow_control_state;
} ottf_console_uart_t;

/**
 * Configures the given UART to be used by the OTTF console.
 *
 * @param console Console pointer
 * @param base_addr The base address of the UART to use.
 */
void ottf_console_configure_uart(ottf_console_t *console, uintptr_t base_addr);

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
 * want to dispatch control flow IRQs for non-main consoles, you must call
 * manually call `ottf_console_uart_flow_control_isr` on the console from your
 * IRQ handler.
 *
 * @param console Pointer to the console.
 */
void ottf_console_uart_flow_control_enable(ottf_console_t *console);

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
 * Manage flow control for UART.
 *
 * See `ottf_console_flow_control`
 */
status_t ottf_console_uart_flow_control(ottf_console_t *console,
                                        ottf_console_flow_control_t ctrl);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_CONSOLE_UART_H_
