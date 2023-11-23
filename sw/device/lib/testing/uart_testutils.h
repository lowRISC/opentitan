// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_UART_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_UART_TESTUTILS_H_

#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_uart.h"

/**
 * Define the available platforms which uart is mapped
 */
typedef enum uart_pinmux_platform_id {
  UartPinmuxPlatformIdHyper310 = 0,
  UartPinmuxPlatformIdDvsim,
  UartPinmuxPlatformIdCount,
} uart_pinmux_platform_id_t;

/**
 * Connect the uart pins to mio pins via pinmux based on the platform the test
 * is running.
 *
 * @param pimmux A pinmux handler.
 * @param kUartIdx The uart instance identifier.
 * @param platform The platform which the test is running.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t uart_testutils_select_pinmux(const dif_pinmux_t *pinmux,
                                      uint8_t kUartIdx,
                                      uart_pinmux_platform_id_t platform);

/**
 * Disconnect the uart input pins from mio pads and wire it to zero.
 *
 * @param pimmux A pinmux handler.
 * @param uart_id The uart instance identifier.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t uart_testutils_detach_pinmux(const dif_pinmux_t *pinmux,
                                      uint8_t uart_id);
#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_UART_TESTUTILS_H_
