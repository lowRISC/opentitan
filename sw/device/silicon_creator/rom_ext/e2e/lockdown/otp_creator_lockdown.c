// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

dif_otp_ctrl_t otp;

status_t test_otp_creator_lockdown(void) {
  uint32_t value;
  LOG_INFO("OTP OwnerSwCfg:");
  TRY(dif_otp_ctrl_read_blocking(&otp, kDifOtpCtrlPartitionOwnerSwCfg, 0,
                                 &value, sizeof(value)));
  LOG_INFO("OTP OwnerSwCfg word 0 = %x", value);

  // If the creator partition has been locked down, this read should cause a
  // fault.
  LOG_INFO("OTP CreatorSwCfg:");
  TRY(dif_otp_ctrl_read_blocking(&otp, kDifOtpCtrlPartitionCreatorSwCfg, 0,
                                 &value, sizeof(value)));
  LOG_INFO("OTP CreatorSwCfg word 0 = %x", value);

  return OK_STATUS();
}

bool test_main(void) {
  CHECK_DIF_OK(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp));

  // Since the ePMP locks down the OTP register space, we cannot call
  // dif_otp_ctrl_configure here.

  status_t sts = test_otp_creator_lockdown();
  if (status_err(sts)) {
    LOG_ERROR("otp_creator_lockdown: %r", sts);
  }
  return status_ok(sts);
}
