// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_OTP_CTRL_H_
#define OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_OTP_CTRL_H_

#include <stdint.h>

#include "sw/device/lib/devicetables/dt.h"

typedef enum {
  kDtOtpCtrlRegBlockCore = 0,
  kDtOtpCtrlRegBlockPrim = 1,
  kDtOtpCtrlRegBlockCount = 2,
} dt_otp_ctrl_reg_block_t;

typedef enum {
  kDtOtpCtrlIrqTypeOtpOperationDone = 0,
  kDtOtpCtrlIrqTypeOtpError = 1,
  kDtOtpCtrlIrqTypeCount = 2,
} dt_otp_ctrl_irq_type_t;

typedef enum {
  kDtOtpCtrlClockClk = 0,
  kDtOtpCtrlClockEdn = 1,
  kDtOtpCtrlClockCount = 2,
} dt_otp_ctrl_clock_t;

typedef enum {
  kDtOtpCtrlPinctrlOutputTest0 = 0,
  kDtOtpCtrlPinctrlOutputTest1 = 1,
  kDtOtpCtrlPinctrlOutputTest2 = 2,
  kDtOtpCtrlPinctrlOutputTest3 = 3,
  kDtOtpCtrlPinctrlOutputTest4 = 4,
  kDtOtpCtrlPinctrlOutputTest5 = 5,
  kDtOtpCtrlPinctrlOutputTest6 = 6,
  kDtOtpCtrlPinctrlOutputTest7 = 7,
  kDtOtpCtrlPinctrlInputCount = 0,
  kDtOtpCtrlPinctrlOutputCount = 8,
} dt_otp_ctrl_pinctrl_t;

#endif  // OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_OTP_CTRL_H_
