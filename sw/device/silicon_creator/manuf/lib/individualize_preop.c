// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/manuf/lib/individualize_preop.h"

#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/silicon_creator/manuf/lib/otp_img.h"
#include "sw/device/silicon_creator/manuf/lib/otp_img_types.h"

status_t manuf_individualize_device_sw_cfg(const dif_otp_ctrl_t *otp_ctrl) {
  TRY(otp_img_write(otp_ctrl, kDifOtpCtrlPartitionCreatorSwCfg,
                    kOtpKvCreatorSwCfg, kOtpKvCreatorSwCfgSize));
  TRY(otp_img_write(otp_ctrl, kDifOtpCtrlPartitionOwnerSwCfg, kOtpKvOwnerSwCfg,
                    kOtpKvOwnerSwCfgSize));
  return OK_STATUS();
}
