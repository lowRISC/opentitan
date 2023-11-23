// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/uart_testutils.h"

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "uart_regs.h"  // Generated.

#define MODULE_ID MAKE_MODULE_ID('u', 't', 'u')

/**
 * This table stores the pins for all UART instances of Earlgrey.
 */
static const pinmux_testutils_peripheral_pin_t kUartPinmuxPins[] = {
    // UART0.
    {
        .peripheral_in = kTopEarlgreyPinmuxPeripheralInUart0Rx,
        .outsel = kTopEarlgreyPinmuxOutselUart0Tx,
    },
    // UART1.
    {
        .peripheral_in = kTopEarlgreyPinmuxPeripheralInUart1Rx,
        .outsel = kTopEarlgreyPinmuxOutselUart1Tx,
    },
    // UART2.
    {
        .peripheral_in = kTopEarlgreyPinmuxPeripheralInUart2Rx,
        .outsel = kTopEarlgreyPinmuxOutselUart2Tx,
    },
    // UART3.
    {
        .peripheral_in = kTopEarlgreyPinmuxPeripheralInUart3Rx,
        .outsel = kTopEarlgreyPinmuxOutselUart3Tx,
    },
};

/**
 * This table stores UART pin mappings for different platforms.
 * This is used to connect UART instances to mio pins based on the platform.
 */
static const pinmux_testutils_mio_pin_t
    kUartPlatformPins[UartPinmuxPlatformIdCount][4] = {
        // Hyper310 bitstream.
        [UartPinmuxPlatformIdHyper310] =
            {// UART0.
             {
                 .mio_out = kTopEarlgreyPinmuxMioOutIoc4,
                 .insel = kTopEarlgreyPinmuxInselIoc3,
             },
             // UART1.
             {
                 .mio_out = kTopEarlgreyPinmuxMioOutIoc4,
                 .insel = kTopEarlgreyPinmuxInselIoc3,
             },
             // UART2.
             {
                 .mio_out = kTopEarlgreyPinmuxMioOutIoc4,
                 .insel = kTopEarlgreyPinmuxInselIoc3,
             },
             // UART3.
             {
                 .mio_out = kTopEarlgreyPinmuxMioOutIoc4,
                 .insel = kTopEarlgreyPinmuxInselIoc3,
             }},
        // DV.
        [UartPinmuxPlatformIdDvsim] = {
            // UART0.
            {
                .mio_out = kTopEarlgreyPinmuxMioOutIoc4,
                .insel = kTopEarlgreyPinmuxInselIoc3,
            },
            // UART1.
            {
                .mio_out = kTopEarlgreyPinmuxMioOutIob5,
                .insel = kTopEarlgreyPinmuxInselIob4,
            },
            // UART2.
            {
                .mio_out = kTopEarlgreyPinmuxMioOutIoa5,
                .insel = kTopEarlgreyPinmuxInselIoa4,
            },
            // UART3.
            {
                .mio_out = kTopEarlgreyPinmuxMioOutIoa1,
                .insel = kTopEarlgreyPinmuxInselIoa0,
            }}};

status_t uart_testutils_select_pinmux(const dif_pinmux_t *pinmux,
                                      uint8_t uart_id,
                                      uart_pinmux_platform_id_t platform) {
  TRY_CHECK(platform < UartPinmuxPlatformIdCount &&
                uart_id < ARRAYSIZE(kUartPinmuxPins),
            "Index out of bounds");

  TRY(dif_pinmux_input_select(pinmux, kUartPinmuxPins[uart_id].peripheral_in,
                              kUartPlatformPins[platform][uart_id].insel));
  TRY(dif_pinmux_output_select(pinmux,
                               kUartPlatformPins[platform][uart_id].mio_out,
                               kUartPinmuxPins[uart_id].outsel));

  return OK_STATUS();
}

status_t uart_testutils_detach_pinmux(const dif_pinmux_t *pinmux,
                                      uint8_t uart_id) {
  TRY_CHECK(uart_id < ARRAYSIZE(kUartPinmuxPins), "Index out of bounds");

  TRY(dif_pinmux_input_select(pinmux, kUartPinmuxPins[uart_id].peripheral_in,
                              kTopEarlgreyPinmuxInselConstantZero));

  return OK_STATUS();
}
