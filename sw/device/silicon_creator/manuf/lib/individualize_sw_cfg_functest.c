// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/manuf/lib/individualize_sw_cfg.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

/**
 * DIF Handles.
 *
 * Keep this list sorted in alphabetical order.
 */
static dif_otp_ctrl_t otp_ctrl;
static dif_rstmgr_t rstmgr;

/**
 * Initializes all DIF handles used in this module.
 */
static status_t peripheral_handles_init(void) {
  TRY(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp_ctrl));
  TRY(dif_rstmgr_init(mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR),
                      &rstmgr));
  return OK_STATUS();
}

/**
 * Perform software reset.
 */
void sw_reset(void) {
  rstmgr_testutils_reason_clear();
  CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));
  wait_for_interrupt();
}

bool test_main(void) {
  CHECK_STATUS_OK(peripheral_handles_init());

  if (!status_ok(manuf_individualize_device_creator_sw_cfg_check(&otp_ctrl))) {
    CHECK_STATUS_OK(manuf_individualize_device_creator_sw_cfg(&otp_ctrl));
    sw_reset();
  }

  if (!status_ok(manuf_individualize_device_owner_sw_cfg_check(&otp_ctrl))) {
    CHECK_STATUS_OK(manuf_individualize_device_owner_sw_cfg(&otp_ctrl));
    sw_reset();
  }

  return true;
}
