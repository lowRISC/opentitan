// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_CONSOLE_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_CONSOLE_H_

#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_uart.h"

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
 * Returns a pointer to the OTTF console device DIF handle.
 */
void *ottf_console_get(void);

/**
 * Initializes the OTTF console device and connects to the printf buffer.
 */
void ottf_console_init(void);

/**
 * Manage flow control by inspecting the OTTF console device's receive FIFO.
 *
 * @param uart A UART handle.
 * @param ctrl Set the next desired flow-control state.
 * @return The new state.
 */
status_t ottf_console_flow_control(const dif_uart_t *uart,
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
 */
void ottf_console_flow_control_enable(void);

/**
 * Returns the number of OTTF console flow control interrupts that have
 * occurred.
 */
uint32_t ottf_console_get_flow_control_irqs(void);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_CONSOLE_H_
