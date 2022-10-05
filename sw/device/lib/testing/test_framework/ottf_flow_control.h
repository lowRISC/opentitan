// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_FLOW_CONTROL_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_FLOW_CONTROL_H_
#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_uart.h"

/**
 * Flow control state.
 */
typedef enum flow_control {
  /** No flow control enabled. */
  kFlowControlNone = 0,
  /** Automatically determine the next flow control state. */
  kFlowControlAuto = 1,
  /**
   * Flow control is in the `Resume` state (safe to receive).
   * This is also the ASCII code for `XON`.
   */
  kFlowControlResume = 17,
  /**
   * Flow control is in the `Pause` state (risk of overrun).
   * This is also the ASCII code for `XOFF`.
   */
  kFlowControlPause = 19,
} flow_control_t;

/**
 * Manage flow control by inspecting the UART receive FIFO.
 *
 * @param uart A UART handle.
 * @param ctrl Set the next desired flow-control state.
 * @return The new state.
 */
status_t ottf_flow_control(const dif_uart_t *uart, flow_control_t ctrl);

/**
 * Enable flow control for the OTTF console.
 *
 * Enables flow control on the UART associated with the OTTF console. Flow
 * control is managed by enabling the RX watermark ISR and sending a `Pause`
 * (aka XOFF) when the RX FIFO depth reaches 16 bytes.  A `Resume` (aka XON) is
 * sent when the RX FIFO has been drained to 4 bytes.
 *
 */
void ottf_flow_control_enable(void);

/**
 * The number of flow control interrupts that have occurred.
 */
extern uint32_t ottf_flow_control_intr;

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_FLOW_CONTROL_H_
