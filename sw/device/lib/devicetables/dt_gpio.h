// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_GPIO_H_
#define OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_GPIO_H_

#include <stdint.h>

#include "sw/device/lib/devicetables/dt.h"

typedef enum {
  kDtGpioRegBlockCore = 0,
  kDtGpioRegBlockCount = 1,
} dt_gpio_reg_block_t;

typedef enum {
  kDtGpioIrqTypeGpio0 = 0,
  kDtGpioIrqTypeGpio1 = 1,
  kDtGpioIrqTypeGpio2 = 2,
  kDtGpioIrqTypeGpio3 = 3,
  kDtGpioIrqTypeGpio4 = 4,
  kDtGpioIrqTypeGpio5 = 5,
  kDtGpioIrqTypeGpio6 = 6,
  kDtGpioIrqTypeGpio7 = 7,
  kDtGpioIrqTypeGpio8 = 8,
  kDtGpioIrqTypeGpio9 = 9,
  kDtGpioIrqTypeGpio10 = 10,
  kDtGpioIrqTypeGpio11 = 11,
  kDtGpioIrqTypeGpio12 = 12,
  kDtGpioIrqTypeGpio13 = 13,
  kDtGpioIrqTypeGpio14 = 14,
  kDtGpioIrqTypeGpio15 = 15,
  kDtGpioIrqTypeGpio16 = 16,
  kDtGpioIrqTypeGpio17 = 17,
  kDtGpioIrqTypeGpio18 = 18,
  kDtGpioIrqTypeGpio19 = 19,
  kDtGpioIrqTypeGpio20 = 20,
  kDtGpioIrqTypeGpio21 = 21,
  kDtGpioIrqTypeGpio22 = 22,
  kDtGpioIrqTypeGpio23 = 23,
  kDtGpioIrqTypeGpio24 = 24,
  kDtGpioIrqTypeGpio25 = 25,
  kDtGpioIrqTypeGpio26 = 26,
  kDtGpioIrqTypeGpio27 = 27,
  kDtGpioIrqTypeGpio28 = 28,
  kDtGpioIrqTypeGpio29 = 29,
  kDtGpioIrqTypeGpio30 = 30,
  kDtGpioIrqTypeGpio31 = 31,
  kDtGpioIrqTypeCount = 32,
} dt_gpio_irq_type_t;

typedef enum {
  kDtGpioClockClk = 0,
  kDtGpioClockCount = 1,
} dt_gpio_clock_t;

typedef enum {
  kDtGpioPinctrlInoutGpio0 = 0,
  kDtGpioPinctrlInoutGpio1 = 1,
  kDtGpioPinctrlInoutGpio2 = 2,
  kDtGpioPinctrlInoutGpio3 = 3,
  kDtGpioPinctrlInoutGpio4 = 4,
  kDtGpioPinctrlInoutGpio5 = 5,
  kDtGpioPinctrlInoutGpio6 = 6,
  kDtGpioPinctrlInoutGpio7 = 7,
  kDtGpioPinctrlInoutGpio8 = 8,
  kDtGpioPinctrlInoutGpio9 = 9,
  kDtGpioPinctrlInoutGpio10 = 10,
  kDtGpioPinctrlInoutGpio11 = 11,
  kDtGpioPinctrlInoutGpio12 = 12,
  kDtGpioPinctrlInoutGpio13 = 13,
  kDtGpioPinctrlInoutGpio14 = 14,
  kDtGpioPinctrlInoutGpio15 = 15,
  kDtGpioPinctrlInoutGpio16 = 16,
  kDtGpioPinctrlInoutGpio17 = 17,
  kDtGpioPinctrlInoutGpio18 = 18,
  kDtGpioPinctrlInoutGpio19 = 19,
  kDtGpioPinctrlInoutGpio20 = 20,
  kDtGpioPinctrlInoutGpio21 = 21,
  kDtGpioPinctrlInoutGpio22 = 22,
  kDtGpioPinctrlInoutGpio23 = 23,
  kDtGpioPinctrlInoutGpio24 = 24,
  kDtGpioPinctrlInoutGpio25 = 25,
  kDtGpioPinctrlInoutGpio26 = 26,
  kDtGpioPinctrlInoutGpio27 = 27,
  kDtGpioPinctrlInoutGpio28 = 28,
  kDtGpioPinctrlInoutGpio29 = 29,
  kDtGpioPinctrlInoutGpio30 = 30,
  kDtGpioPinctrlInoutGpio31 = 31,
  kDtGpioPinctrlInputCount = 32,
  kDtGpioPinctrlOutputCount = 32,
} dt_gpio_pinctrl_t;

#endif  // OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_GPIO_H_
