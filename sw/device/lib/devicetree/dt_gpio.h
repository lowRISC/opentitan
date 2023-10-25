// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DEVICETREE_DT_GPIO_H_
#define OPENTITAN_SW_DEVICE_LIB_DEVICETREE_DT_GPIO_H_

#include <stdint.h>

typedef enum {
  kDtGpioIrqGpio0 = 0,
  kDtGpioIrqGpio1,
  kDtGpioIrqGpio2,
  kDtGpioIrqGpio3,
  kDtGpioIrqGpio4,
  kDtGpioIrqGpio5,
  kDtGpioIrqGpio6,
  kDtGpioIrqGpio7,
  kDtGpioIrqGpio8,
  kDtGpioIrqGpio9,
  kDtGpioIrqGpio10,
  kDtGpioIrqGpio11,
  kDtGpioIrqGpio12,
  kDtGpioIrqGpio13,
  kDtGpioIrqGpio14,
  kDtGpioIrqGpio15,
  kDtGpioIrqGpio16,
  kDtGpioIrqGpio17,
  kDtGpioIrqGpio18,
  kDtGpioIrqGpio19,
  kDtGpioIrqGpio20,
  kDtGpioIrqGpio21,
  kDtGpioIrqGpio22,
  kDtGpioIrqGpio23,
  kDtGpioIrqGpio24,
  kDtGpioIrqGpio25,
  kDtGpioIrqGpio26,
  kDtGpioIrqGpio27,
  kDtGpioIrqGpio28,
  kDtGpioIrqGpio29,
  kDtGpioIrqGpio30,
  kDtGpioIrqGpio31,
  kDtGpioIrqTypeCount,
} dt_gpio_irq_type_t;

extern uint32_t dt_gpio_num_devices(void);
extern int32_t dt_gpio_device_id(uint32_t dev_idx);
extern uintptr_t dt_gpio_reg_addr(uint32_t dev_idx);
extern int32_t dt_gpio_irq_id(uint32_t dev_idx, dt_gpio_irq_type_t irq_type);

#endif  // OPENTITAN_SW_DEVICE_LIB_DEVICETREE_DT_GPIO_H_
