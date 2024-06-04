// Copyright lowRISC contributors (OpenTitan project).
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
  kUartPinmuxPlatformIdFpgaCw310 = 0,
  kUartPinmuxPlatformIdDvsim,
  kUartPinmuxPlatformIdSilicon,
  kUartPinmuxPlatformIdCount,
} uart_pinmux_platform_id_t;

/**
 * Define the available external channels that a UART could be connected to.
 */
typedef enum uart_pinmux_channel {
  kUartPinmuxChannelConsole,
  kUartPinmuxChannelDut,
  kUartPinmuxChannelCount,
} uart_pinmux_channel_t;

typedef struct uart_cfg_params {
  uint32_t base_addr;
  uint32_t peripheral_id;
  uint32_t irq_tx_watermark_id;
  uint32_t irq_tx_empty_id;
  uint32_t irq_rx_watermark_id;
  uint32_t irq_tx_done_id;
  uint32_t irq_rx_overflow_id;
  uint32_t irq_rx_frame_err_id;
  uint32_t irq_rx_break_err_id;
  uint32_t irq_rx_timeout_id;
  uint32_t irq_rx_parity_err_id;
} uart_cfg_params_t;

/**
 * Connect the uart pins to mio pins via pinmux based on the platform the test
 * is running.
 *
 * @param pimmux A pinmux handler.
 * @param uart_idx The index of the UART to configure.
 * @param platform The platform which the test is running.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t uart_testutils_select_pinmux(const dif_pinmux_t *pinmux,
                                      uint8_t uart_idx,
                                      uart_pinmux_channel_t channel);

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

/**
 * Look up the configuration parameters for a given UART instance.
 *
 * @param uart_idx The index of the UART being configured.
 * @param[out] params Pointer to the struct to write the parameters to.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t uart_testutils_cfg_params(uint8_t uart_idx, uart_cfg_params_t *params);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_UART_TESTUTILS_H_
