// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/devicetree/dt.h"

#include <zephyr/devicetree.h>

typedef struct dt_device_uart {
  uintptr_t reg_addr[1];
} dt_device_uart_t;

static const dt_device_uart_t uart[] = {
    [0] =
        {
            .reg_addr = {DT_REG_ADDR(DT_NODELABEL(uart0))},
        },
    [1] =
        {
            .reg_addr = {DT_REG_ADDR(DT_NODELABEL(uart1))},
        },
    [2] =
        {
            .reg_addr = {DT_REG_ADDR(DT_NODELABEL(uart2))},
        },
    [3] =
        {
            .reg_addr = {DT_REG_ADDR(DT_NODELABEL(uart3))},
        },
};

// This could be another way to do it
uintptr_t dt_reg_addr(dt_device_t dev, uint32_t dev_idx,
                      uint32_t reg_iface_idx) {
  switch (dev) {
    case kDtDeviceUart:
      return uart[dev_idx].reg_addr[reg_iface_idx];
      break;
    default:
      return 0;
      break;
  };
  return 0;
}
