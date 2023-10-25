// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DEVICETREE_DT_OTP_CTRL_H_
#define OPENTITAN_SW_DEVICE_LIB_DEVICETREE_DT_OTP_CTRL_H_

#include <stdint.h>

typedef enum {
  kDtOtpCtrlRegBlockCore = 0,
  kDtOtpCtrlRegBlockPrim,
  kDtOtpCtrlRegBlockCount,
} dt_otp_ctrl_reg_block_t;

typedef enum {
  kDtOtpCtrlIrqOtpOperationDone = 0,
  kDtOtpCtrlIrqOtpError,
  kDtOtpCtrlIrqTypeCount,
} dt_otp_ctrl_irq_type_t;

extern uint32_t dt_otp_ctrl_num_devices(void);
extern int32_t dt_otp_ctrl_device_id(uint32_t dev_idx);
extern uintptr_t dt_otp_ctrl_reg_addr(uint32_t dev_idx,
                                      dt_otp_ctrl_reg_block_t reg_block);
extern int32_t dt_otp_ctrl_irq_id(uint32_t dev_idx,
                                  dt_otp_ctrl_irq_type_t irq_type);

#endif  // OPENTITAN_SW_DEVICE_LIB_DEVICETREE_DT_OTP_CTRL_H_
