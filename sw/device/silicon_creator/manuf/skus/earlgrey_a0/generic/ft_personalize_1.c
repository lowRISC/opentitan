// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/lc_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/silicon_creator/manuf/lib/individualize_sw_cfg.h"
#include "sw/device/silicon_creator/manuf/lib/personalize.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

static dif_lc_ctrl_t lc_ctrl;
static dif_otp_ctrl_t otp_ctrl;

/**
 * Initializes all DIF handles used in this SRAM program.
 */
static status_t peripheral_handles_init(void) {
  TRY(dif_lc_ctrl_init(mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_BASE_ADDR),
                       &lc_ctrl));
  TRY(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp_ctrl));
  return OK_STATUS();
}

bool test_main(void) {
  CHECK_STATUS_OK(peripheral_handles_init());

  // Check we are in a mission mode LC state (i.e., DEV, PROD, or PROD_END).
  CHECK_STATUS_OK(lc_ctrl_testutils_operational_state_check(&lc_ctrl));

  // Provision OTP Secret1 partition and keymgr and complete provisioning of OTP
  // CreatorSwCfg partition.
  if (!status_ok(manuf_personalize_device_secret1_check(&otp_ctrl))) {
    CHECK_STATUS_OK(manuf_personalize_device_secret1(&lc_ctrl, &otp_ctrl));
  }
  if (!status_ok(manuf_individualize_device_creator_sw_cfg_check(&otp_ctrl))) {
    CHECK_STATUS_OK(
        manuf_individualize_device_flash_data_default_cfg(&otp_ctrl));
    CHECK_STATUS_OK(manuf_individualize_device_creator_sw_cfg_lock(&otp_ctrl));
  }

  return true;
}
