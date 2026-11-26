// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_UART_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_UART_TESTUTILS_H_

#include <stdint.h>

#include "hw/top/dt/uart.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_uart.h"

/**
 * Connect the uart pins to its mio pads via pinmux.
 *
 * Each UART uses a fixed pad pair, which is wired to a host UART on the boards
 * and to a UART agent in DV.
 *
 * @param pimmux A pinmux handler.
 * @param uart_idx The index of the UART to configure.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t uart_testutils_select_pinmux(const dif_pinmux_t *pinmux,
                                      uint8_t uart_idx);

/**
 * Disconnect the uart input pins from mio pads and wire it to zero.
 *
 * @param pimmux A pinmux handler.
 * @param uart_id The index of the UART to configure.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t uart_testutils_detach_pinmux(const dif_pinmux_t *pinmux,
                                      uint8_t uart_idx);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_UART_TESTUTILS_H_
