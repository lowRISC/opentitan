// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_PWM_H_
#define OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_PWM_H_

#include <stdint.h>

#include "sw/device/lib/devicetables/dt.h"

typedef enum {
  kDtPwmRegBlockCore = 0,
  kDtPwmRegBlockCount = 1,
} dt_pwm_reg_block_t;

typedef enum {
  kDtPwmClockClk = 0,
  kDtPwmClockCore = 1,
  kDtPwmClockCount = 2,
} dt_pwm_clock_t;

typedef enum {
  kDtPwmPinctrlOutputPwm0 = 0,
  kDtPwmPinctrlOutputPwm1 = 1,
  kDtPwmPinctrlOutputPwm2 = 2,
  kDtPwmPinctrlOutputPwm3 = 3,
  kDtPwmPinctrlOutputPwm4 = 4,
  kDtPwmPinctrlOutputPwm5 = 5,
  kDtPwmPinctrlInputCount = 0,
  kDtPwmPinctrlOutputCount = 6,
} dt_pwm_pinctrl_t;

#endif  // OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_PWM_H_
