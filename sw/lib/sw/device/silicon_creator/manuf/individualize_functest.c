// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/ip/flash_ctrl/dif/dif_flash_ctrl.h"
#include "sw/ip/flash_ctrl/driver/flash_ctrl.h"
#include "sw/ip/lc_ctrl/dif/dif_lc_ctrl.h"
#include "sw/ip/lc_ctrl/driver/lc_ctrl.h"
#include "sw/ip/otp_ctrl/dif/dif_otp_ctrl.h"
#include "sw/ip/otp_ctrl/driver/otp_ctrl.h"
#include "sw/ip/rstmgr/dif/dif_rstmgr.h"
#include "sw/ip/rstmgr/driver/rstmgr.h"
#include "sw/ip/rstmgr/test/utils/rstmgr_testutils.h"
#include "sw/lib/sw/device/base/status.h"
#include "sw/lib/sw/device/silicon_creator/manuf/individualize.h"

#include "flash_ctrl_regs.h"  // Generated
#include "lc_ctrl_regs.h"     // Generated
#include "otp_ctrl_regs.h"    // Generated

OTTF_DEFINE_TEST_CONFIG();

/**
 * DIF Handles.
 *
 * Keep this list sorted in alphabetical order.
 */
static dif_flash_ctrl_state_t flash_state;
static dif_lc_ctrl_t lc_ctrl;
static dif_otp_ctrl_t otp_ctrl;
static dif_rstmgr_t rstmgr;

/**
 * Initializes all DIF handles used in this module.
 */
static status_t peripheral_handles_init(void) {
  TRY(dif_flash_ctrl_init_state(
      &flash_state, mmio_region_from_addr(kFlashCtrlCoreBaseAddr[0])));
  TRY(dif_lc_ctrl_init(mmio_region_from_addr(kLcCtrlRegsBaseAddr[0]),
                       &lc_ctrl));
  TRY(dif_otp_ctrl_init(mmio_region_from_addr(kOtpCtrlCoreBaseAddr[0]),
                        &otp_ctrl));
  TRY(dif_rstmgr_init(mmio_region_from_addr(kRstmgrAonBaseAddr[0]), &rstmgr));
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

  if (!status_ok(individualize_dev_hw_cfg0_end(&otp_ctrl))) {
    CHECK_STATUS_OK(
        individualize_dev_hw_cfg0_start(&flash_state, &lc_ctrl, &otp_ctrl));
    sw_reset();
  }

  if (!status_ok(individualize_dev_hw_cfg1_end(&otp_ctrl))) {
    CHECK_STATUS_OK(
        individualize_dev_hw_cfg1_start(&flash_state, &lc_ctrl, &otp_ctrl));
    sw_reset();
  }

  if (!status_ok(individualize_dev_secret1_end(&otp_ctrl))) {
    CHECK_STATUS_OK(individualize_dev_secret1_start(&lc_ctrl, &otp_ctrl));
    sw_reset();
  }

  return true;
}
