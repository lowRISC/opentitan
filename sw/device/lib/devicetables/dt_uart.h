// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_UART_H_
#define OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_UART_H_

#include <stdint.h>

#include "sw/device/lib/devicetables/dt.h"

typedef enum {
  kDtUartRegBlockCore = 0,
  kDtUartRegBlockCount = 1,
} dt_uart_reg_block_t;

typedef enum {
  kDtUartIrqTypeTxWatermark = 0,
  kDtUartIrqTypeRxWatermark = 1,
  kDtUartIrqTypeTxEmpty = 2,
  kDtUartIrqTypeRxOverflow = 3,
  kDtUartIrqTypeRxFrameErr = 4,
  kDtUartIrqTypeRxBreakErr = 5,
  kDtUartIrqTypeRxTimeout = 6,
  kDtUartIrqTypeRxParityErr = 7,
  kDtUartIrqTypeCount = 8,
} dt_uart_irq_type_t;

typedef enum {
  kDtUartClockClk = 0,
  kDtUartClockCount = 1,
} dt_uart_clock_t;

typedef enum {
  kDtUartPinctrlInputRx = 0,
  kDtUartPinctrlOutputTx = 1,
  kDtUartPinctrlInputCount = 1,
  kDtUartPinctrlOutputCount = 2,
} dt_uart_pinctrl_t;

#endif  // OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_UART_H_
