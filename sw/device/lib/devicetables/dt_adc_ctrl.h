// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_ADC_CTRL_H_
#define OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_ADC_CTRL_H_

#include <stdint.h>

#include "sw/device/lib/devicetables/dt.h"

typedef enum {
  kDtAdcCtrlRegBlockCore = 0,
  kDtAdcCtrlRegBlockCount = 1,
} dt_adc_ctrl_reg_block_t;

typedef enum {
  kDtAdcCtrlIrqTypeMatchDone = 0,
  kDtAdcCtrlIrqTypeCount = 1,
} dt_adc_ctrl_irq_type_t;

typedef enum {
  kDtAdcCtrlClockClk = 0,
  kDtAdcCtrlClockAon = 1,
  kDtAdcCtrlClockCount = 2,
} dt_adc_ctrl_clock_t;

typedef enum {
  kDtAdcCtrlPinctrlInputCount = 0,
  kDtAdcCtrlPinctrlOutputCount = 0,
} dt_adc_ctrl_pinctrl_t;

#endif  // OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_ADC_CTRL_H_
