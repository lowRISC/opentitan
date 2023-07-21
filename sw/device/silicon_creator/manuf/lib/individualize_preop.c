// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include "sw/device/silicon_creator/manuf/lib/individualize_preop.h"

#include "otp_img_sku_earlgrey_a0_stage_individualize.h"  // Generated.
#include "sw/device/silicon_creator/manuf/lib/otp_img.h"
#include "sw/ip/otp_ctrl/dif/dif_otp_ctrl.h"

status_t individualize_preop_otp_write(const dif_otp_ctrl_t *otp) {
  TRY(otp_img_write(otp, kDifOtpCtrlPartitionCreatorSwCfg, kOtpKvCreatorSwCfg,
                    ARRAYSIZE(kOtpKvCreatorSwCfg)));
  TRY(otp_img_write(otp, kDifOtpCtrlPartitionOwnerSwCfg, kOtpKvOwnerSwCfg,
                    ARRAYSIZE(kOtpKvOwnerSwCfg)));
  return OK_STATUS();
}
