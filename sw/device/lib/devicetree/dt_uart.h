// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DEVICETREE_DT_UART_H_
#define OPENTITAN_SW_DEVICE_LIB_DEVICETREE_DT_UART_H_

#include <stdint.h>

typedef enum {
  kDtUartIrqTxWatermark = 0,
  kDtUartIrqRxWatermark,
  kDtUartIrqTxEmpty,
  kDtUartIrqRxOverflow,
  kDtUartIrqRxFrameErr,
  kDtUartIrqRxBreakErr,
  kDtUartIrqRxTimeout,
  kDtUartIrqRxParityErr,
  kDtUartIrqTypeCount,
} dt_uart_irq_type_t;

extern uint32_t dt_uart_num_devices(void);
extern int32_t dt_uart_device_id(uint32_t dev_idx);
extern uintptr_t dt_uart_reg_addr(uint32_t dev_idx);
extern int32_t dt_uart_irq_id(uint32_t dev_idx, dt_uart_irq_type_t irq_type);

#endif  // OPENTITAN_SW_DEVICE_LIB_DEVICETREE_DT_UART_H_
