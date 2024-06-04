// Copyright lowRISC contributors (OpenTitan project).
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
 * This table stores UART pin mappings for synthesized platforms.
 */
static const pinmux_testutils_mio_pin_t
    kUartSynthPins[kUartPinmuxChannelCount] = {
        [kUartPinmuxChannelConsole] =
            {
                .mio_out = kTopEarlgreyPinmuxMioOutIoc4,
                .insel = kTopEarlgreyPinmuxInselIoc3,
            },
        [kUartPinmuxChannelDut] = {
            .mio_out = kTopEarlgreyPinmuxMioOutIob5,
            .insel = kTopEarlgreyPinmuxInselIob4,
        }};

/**
 * The DV platform is handled separately at the moment: all four UARTs have
 * their own channels that they map to rather than using one channel for the
 * console and second for the DUT.
 */
static const pinmux_testutils_mio_pin_t kUartDvPins[4] = {
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
    }};

static const uart_cfg_params_t kUartCfgParams[4] = {
    (uart_cfg_params_t){
        .base_addr = TOP_EARLGREY_UART0_BASE_ADDR,
        .peripheral_id = kTopEarlgreyPlicPeripheralUart0,
        .irq_tx_watermark_id = kTopEarlgreyPlicIrqIdUart0TxWatermark,
        .irq_tx_empty_id = kTopEarlgreyPlicIrqIdUart0TxEmpty,
        .irq_rx_watermark_id = kTopEarlgreyPlicIrqIdUart0RxWatermark,
        .irq_tx_done_id = kTopEarlgreyPlicIrqIdUart0TxDone,
        .irq_rx_overflow_id = kTopEarlgreyPlicIrqIdUart0RxOverflow,
        .irq_rx_frame_err_id = kTopEarlgreyPlicIrqIdUart0RxFrameErr,
        .irq_rx_break_err_id = kTopEarlgreyPlicIrqIdUart0RxBreakErr,
        .irq_rx_timeout_id = kTopEarlgreyPlicIrqIdUart0RxTimeout,
        .irq_rx_parity_err_id = kTopEarlgreyPlicIrqIdUart0RxParityErr,
    },
    (uart_cfg_params_t){
        .base_addr = TOP_EARLGREY_UART1_BASE_ADDR,
        .peripheral_id = kTopEarlgreyPlicPeripheralUart1,
        .irq_tx_watermark_id = kTopEarlgreyPlicIrqIdUart1TxWatermark,
        .irq_tx_empty_id = kTopEarlgreyPlicIrqIdUart1TxEmpty,
        .irq_rx_watermark_id = kTopEarlgreyPlicIrqIdUart1RxWatermark,
        .irq_tx_done_id = kTopEarlgreyPlicIrqIdUart1TxDone,
        .irq_rx_overflow_id = kTopEarlgreyPlicIrqIdUart1RxOverflow,
        .irq_rx_frame_err_id = kTopEarlgreyPlicIrqIdUart1RxFrameErr,
        .irq_rx_break_err_id = kTopEarlgreyPlicIrqIdUart1RxBreakErr,
        .irq_rx_timeout_id = kTopEarlgreyPlicIrqIdUart1RxTimeout,
        .irq_rx_parity_err_id = kTopEarlgreyPlicIrqIdUart1RxParityErr,
    },
    (uart_cfg_params_t){
        .base_addr = TOP_EARLGREY_UART2_BASE_ADDR,
        .peripheral_id = kTopEarlgreyPlicPeripheralUart2,
        .irq_tx_watermark_id = kTopEarlgreyPlicIrqIdUart2TxWatermark,
        .irq_tx_empty_id = kTopEarlgreyPlicIrqIdUart2TxEmpty,
        .irq_rx_watermark_id = kTopEarlgreyPlicIrqIdUart2RxWatermark,
        .irq_tx_done_id = kTopEarlgreyPlicIrqIdUart2TxDone,
        .irq_rx_overflow_id = kTopEarlgreyPlicIrqIdUart2RxOverflow,
        .irq_rx_frame_err_id = kTopEarlgreyPlicIrqIdUart2RxFrameErr,
        .irq_rx_break_err_id = kTopEarlgreyPlicIrqIdUart2RxBreakErr,
        .irq_rx_timeout_id = kTopEarlgreyPlicIrqIdUart2RxTimeout,
        .irq_rx_parity_err_id = kTopEarlgreyPlicIrqIdUart2RxParityErr,
    },
    (uart_cfg_params_t){
        .base_addr = TOP_EARLGREY_UART3_BASE_ADDR,
        .peripheral_id = kTopEarlgreyPlicPeripheralUart3,
        .irq_tx_watermark_id = kTopEarlgreyPlicIrqIdUart3TxWatermark,
        .irq_tx_empty_id = kTopEarlgreyPlicIrqIdUart3TxEmpty,
        .irq_rx_watermark_id = kTopEarlgreyPlicIrqIdUart3RxWatermark,
        .irq_tx_done_id = kTopEarlgreyPlicIrqIdUart3TxDone,
        .irq_rx_overflow_id = kTopEarlgreyPlicIrqIdUart3RxOverflow,
        .irq_rx_frame_err_id = kTopEarlgreyPlicIrqIdUart3RxFrameErr,
        .irq_rx_break_err_id = kTopEarlgreyPlicIrqIdUart3RxBreakErr,
        .irq_rx_timeout_id = kTopEarlgreyPlicIrqIdUart3RxTimeout,
        .irq_rx_parity_err_id = kTopEarlgreyPlicIrqIdUart3RxParityErr,
    }};

status_t uart_testutils_select_pinmux(const dif_pinmux_t *pinmux,
                                      uint8_t uart_idx,
                                      uart_pinmux_channel_t channel) {
  TRY_CHECK(channel < kUartPinmuxChannelCount &&
                uart_idx < ARRAYSIZE(kUartPinmuxPins),
            "Index out of bounds");

  pinmux_testutils_mio_pin_t mio_pin = kDeviceType == kDeviceSimDV
                                           ? kUartDvPins[uart_idx]
                                           : kUartSynthPins[channel];

  TRY(dif_pinmux_input_select(pinmux, kUartPinmuxPins[uart_idx].peripheral_in,
                              mio_pin.insel));
  TRY(dif_pinmux_output_select(pinmux, mio_pin.mio_out,
                               kUartPinmuxPins[uart_idx].outsel));

  return OK_STATUS();
}

status_t uart_testutils_detach_pinmux(const dif_pinmux_t *pinmux,
                                      uint8_t uart_idx) {
  TRY_CHECK(uart_idx < ARRAYSIZE(kUartPinmuxPins), "Index out of bounds");

  TRY(dif_pinmux_input_select(pinmux, kUartPinmuxPins[uart_idx].peripheral_in,
                              kTopEarlgreyPinmuxInselConstantZero));

  return OK_STATUS();
}

status_t uart_testutils_cfg_params(uint8_t uart_idx,
                                   uart_cfg_params_t *params) {
  TRY_CHECK(uart_idx < ARRAYSIZE(kUartCfgParams), "Index out of bounds");

  *params = kUartCfgParams[uart_idx];

  return OK_STATUS();
}
