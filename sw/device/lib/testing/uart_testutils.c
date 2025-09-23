// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/uart_testutils.h"

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>

#include "hw/top/dt/dt_pinmux.h"
#include "hw/top/dt/dt_uart.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"

#include "hw/top/uart_regs.h"  // Generated.

#define MODULE_ID MAKE_MODULE_ID('u', 't', 'u')

/**
 * Get the UART instance from index.
 *
 * @param uart_idx UART index (0-based).
 * @return UART DT instance, or kDtUartCount if invalid.
 */
static dt_uart_t get_uart_instance(uint8_t uart_idx) {
  if (uart_idx >= kDtUartCount) {
    return kDtUartCount;
  }
  return (dt_uart_t)uart_idx;
}

/**
 * Get the appropriate pads for a UART instance and channel based on the
 * platform. This replicates the original behavior with different mappings for
 * DV vs synthesized platforms.
 *
 * @param uart_dt UART DT instance.
 * @param channel The channel to connect the UART to.
 * @param rx_pad Output parameter for RX pad.
 * @param tx_pad Output parameter for TX pad.
 * @return OK_STATUS if successful, error status otherwise.
 */
static status_t get_uart_pads_for_channel(dt_uart_t uart_dt,
                                          uart_pinmux_channel_t channel,
                                          dt_pad_t *rx_pad, dt_pad_t *tx_pad) {
#if defined(OPENTITAN_IS_DARJEELING)
  // Darjeeling only has UART0 and uses dedicated pads
  if (uart_dt != kDtUart0) {
    return INVALID_ARGUMENT();
  }
  *rx_pad = kDtPadUart0Rx;
  *tx_pad = kDtPadUart0Tx;
#elif defined(OPENTITAN_IS_EARLGREY) || defined(OPENTITAN_IS_ENGLISHBREAKFAST)
  // For Earlgrey and EnglishBreakfast platforms
  // For DV platform, each UART has its own specific mapping
  if (kDeviceType == kDeviceSimDV) {
    switch (uart_dt) {
      case kDtUart0:
        *rx_pad = kDtPadIoc3;
        *tx_pad = kDtPadIoc4;
        break;
      case kDtUart1:
        *rx_pad = kDtPadIob4;
        *tx_pad = kDtPadIob5;
        break;
      case kDtUart2:
        *rx_pad = kDtPadIoa4;
        *tx_pad = kDtPadIoa5;
        break;
      case kDtUart3:
        *rx_pad = kDtPadIoa0;
        *tx_pad = kDtPadIoa1;
        break;
      default:
        return INVALID_ARGUMENT();
    }
  } else {
    // For synthesized platforms, use channel-based mapping
    switch (channel) {
      case kUartPinmuxChannelConsole:
        *rx_pad = kDtPadIoc3;
        *tx_pad = kDtPadIoc4;
        break;
      case kUartPinmuxChannelDut:
        *rx_pad = kDtPadIob4;
        *tx_pad = kDtPadIob5;
        break;
      default:
        return INVALID_ARGUMENT();
    }
  }
#else
  return UNIMPLEMENTED();
#endif

  return OK_STATUS();
}

status_t uart_testutils_select_pinmux(const dif_pinmux_t *pinmux,
                                      uint8_t uart_idx,
                                      uart_pinmux_channel_t channel) {
  TRY_CHECK(channel < kUartPinmuxChannelCount, "Channel out of bounds");

  dt_uart_t uart_dt = get_uart_instance(uart_idx);
  TRY_CHECK(uart_dt < kDtUartCount, "UART index out of bounds");

  // Get peripheral I/O descriptions for RX and TX
  dt_periph_io_t rx_periph_io = dt_uart_periph_io(uart_dt, kDtUartPeriphIoRx);
  dt_periph_io_t tx_periph_io = dt_uart_periph_io(uart_dt, kDtUartPeriphIoTx);

  // Get the appropriate pads for this UART instance and channel
  dt_pad_t rx_pad, tx_pad;
  TRY(get_uart_pads_for_channel(uart_dt, channel, &rx_pad, &tx_pad));

  // Connect RX input using low-level pinmux functions
  TRY(dif_pinmux_input_select(pinmux,
                              dt_periph_io_mio_periph_input(rx_periph_io),
                              dt_pad_mio_insel(rx_pad)));

  // Connect TX output using low-level pinmux functions
  TRY(dif_pinmux_output_select(pinmux, dt_pad_mio_out(tx_pad),
                               dt_periph_io_mio_outsel(tx_periph_io)));

  return OK_STATUS();
}

status_t uart_testutils_detach_pinmux(const dif_pinmux_t *pinmux,
                                      uint8_t uart_idx) {
  dt_uart_t uart_dt = get_uart_instance(uart_idx);
  TRY_CHECK(uart_dt < kDtUartCount, "UART index out of bounds");

  // Get peripheral I/O description for RX
  dt_periph_io_t rx_periph_io = dt_uart_periph_io(uart_dt, kDtUartPeriphIoRx);

  // Disconnect RX input by connecting to constant zero using low-level function
  TRY(dif_pinmux_input_select(pinmux,
                              dt_periph_io_mio_periph_input(rx_periph_io),
                              kDtPinmuxInselConstantZero));

  return OK_STATUS();
}

status_t uart_testutils_cfg_params(uint8_t uart_idx,
                                   uart_cfg_params_t *params) {
  dt_uart_t uart_dt = get_uart_instance(uart_idx);
  TRY_CHECK(uart_dt < kDtUartCount, "UART index out of bounds");

  params->base_addr = dt_uart_reg_block(uart_dt, kDtUartRegBlockCore);

  // Get peripheral ID from DT (convert from instance ID)
  dt_instance_id_t instance_id = dt_uart_instance_id(uart_dt);
  params->peripheral_id =
      instance_id;  // This assumes PLIC peripheral ID matches instance ID

  // Get IRQ IDs from DT
  params->irq_tx_watermark_id =
      dt_uart_irq_to_plic_id(uart_dt, kDtUartIrqTxWatermark);
  params->irq_tx_empty_id = dt_uart_irq_to_plic_id(uart_dt, kDtUartIrqTxEmpty);
  params->irq_rx_watermark_id =
      dt_uart_irq_to_plic_id(uart_dt, kDtUartIrqRxWatermark);
  params->irq_tx_done_id = dt_uart_irq_to_plic_id(uart_dt, kDtUartIrqTxDone);
  params->irq_rx_overflow_id =
      dt_uart_irq_to_plic_id(uart_dt, kDtUartIrqRxOverflow);
  params->irq_rx_frame_err_id =
      dt_uart_irq_to_plic_id(uart_dt, kDtUartIrqRxFrameErr);
  params->irq_rx_break_err_id =
      dt_uart_irq_to_plic_id(uart_dt, kDtUartIrqRxBreakErr);
  params->irq_rx_timeout_id =
      dt_uart_irq_to_plic_id(uart_dt, kDtUartIrqRxTimeout);
  params->irq_rx_parity_err_id =
      dt_uart_irq_to_plic_id(uart_dt, kDtUartIrqRxParityErr);

  return OK_STATUS();
}
