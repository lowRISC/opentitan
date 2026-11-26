// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/uart_testutils.h"

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>

#include "hw/top/dt/pinmux.h"
#include "sw/device/lib/arch/device.h"
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
 * Get the pads of a UART instance.
 *
 * @param uart_dt UART DT instance.
 * @param rx_pad Output parameter for RX pad.
 * @param tx_pad Output parameter for TX pad.
 * @return OK_STATUS if successful, error status otherwise.
 */
static status_t get_uart_pads(dt_uart_t uart_dt, dt_pad_t *rx_pad,
                              dt_pad_t *tx_pad) {
#if defined(OPENTITAN_IS_DARJEELING)
  // Darjeeling only has UART0 and uses dedicated pads
  if (uart_dt != kDtUart0) {
    return INVALID_ARGUMENT();
  }
  *rx_pad = kDtPadUart0Rx;
  *tx_pad = kDtPadUart0Tx;
#elif defined(OPENTITAN_IS_EARLGREY)
  // Each UART can only reach a few pads. In DV these pairs connect to the UART
  // agents so keep AssignedUart*Ios in chip_if.sv in sync. On the CW340 they
  // connect to the HyperDebug UARTs. HD's UART1 and UART3 use IOR pads there.
  bool fpga = kDeviceType == kDeviceFpgaCw340;
  switch (uart_dt) {
    case kDtUart0:
      *rx_pad = kDtPadIoc3;
      *tx_pad = kDtPadIoc4;
      break;
    case kDtUart1:
      // On the CW340 the HyperDebug UART4 nets carry IOR5/IOR6, IOA0/IOA1 are
      // the JTAG pads.
      *rx_pad = fpga ? kDtPadIor5 : kDtPadIoa0;
      *tx_pad = fpga ? kDtPadIor6 : kDtPadIoa1;
      break;
    case kDtUart2:
      *rx_pad = kDtPadIob4;
      *tx_pad = kDtPadIob5;
      break;
    case kDtUart3:
      // On the CW340 the HyperDebug UART5 nets carry IOR3/IOR4, IOA4/IOA5 are
      // the JTAG pads.
      *rx_pad = fpga ? kDtPadIor3 : kDtPadIoa4;
      *tx_pad = fpga ? kDtPadIor4 : kDtPadIoa5;
      break;
    default:
      return INVALID_ARGUMENT();
  }
#elif defined(OPENTITAN_IS_ENGLISHBREAKFAST)
  switch (uart_dt) {
    case kDtUart0:
      *rx_pad = kDtPadIoc3;
      *tx_pad = kDtPadIoc4;
      break;
    case kDtUart1:
      *rx_pad = kDtPadIob4;
      *tx_pad = kDtPadIob5;
      break;
    default:
      return INVALID_ARGUMENT();
  }
#else
  return UNIMPLEMENTED();
#endif

  return OK_STATUS();
}

status_t uart_testutils_select_pinmux(const dif_pinmux_t *pinmux,
                                      uint8_t uart_idx) {
  dt_uart_t uart_dt = get_uart_instance(uart_idx);
  TRY_CHECK(uart_dt < kDtUartCount, "UART index out of bounds");

  // Get peripheral I/O descriptions for RX and TX
  dt_periph_io_t rx_periph_io = dt_uart_periph_io(uart_dt, kDtUartPeriphIoRx);
  dt_periph_io_t tx_periph_io = dt_uart_periph_io(uart_dt, kDtUartPeriphIoTx);

  // Get the pads of this UART instance
  dt_pad_t rx_pad, tx_pad;
  TRY(get_uart_pads(uart_dt, &rx_pad, &tx_pad));

  // Connect RX input using low-level pinmux functions
  TRY(dif_pinmux_mio_select_input(pinmux, rx_periph_io, rx_pad));

  // Connect TX output using low-level pinmux functions
  TRY(dif_pinmux_mio_select_output(pinmux, tx_pad, tx_periph_io));

  return OK_STATUS();
}

status_t uart_testutils_detach_pinmux(const dif_pinmux_t *pinmux,
                                      uint8_t uart_idx) {
  dt_uart_t uart_dt = get_uart_instance(uart_idx);
  TRY_CHECK(uart_dt < kDtUartCount, "UART index out of bounds");

  // Get peripheral I/O description for RX
  dt_periph_io_t rx_periph_io = dt_uart_periph_io(uart_dt, kDtUartPeriphIoRx);

  // Disconnect RX input by connecting to constant zero using low-level function
  TRY(dif_pinmux_mio_select_input(pinmux, rx_periph_io, kDtPadConstantZero));

  return OK_STATUS();
}
