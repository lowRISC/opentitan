// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/testing/json/provisioning_data.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/silicon_creator/manuf/lib/provisioning.h"

#include "flash_ctrl_regs.h"  // Generated
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "lc_ctrl_regs.h"   // Generated
#include "otp_ctrl_regs.h"  // Generated

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

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
      &flash_state,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
  TRY(dif_lc_ctrl_init(mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_BASE_ADDR),
                       &lc_ctrl));
  TRY(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp_ctrl));
  TRY(dif_rstmgr_init(mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR),
                      &rstmgr));
  return OK_STATUS();
}

bool test_main(void) {
  ujson_t uj = ujson_ottf_console();
  CHECK_STATUS_OK(peripheral_handles_init());

  dif_rstmgr_reset_info_bitfield_t info = rstmgr_testutils_reason_get();
  if (info & kDifRstmgrResetInfoPor) {
    LOG_INFO("provisioning start");

    manuf_provisioning_t export_data = {
        .wrapped_rma_unlock_token =
            {
                .data = {0},
                .ecc_pk_device_x = {0},
                .ecc_pk_device_y = {0},
            },
    };
    CHECK_STATUS_OK(provisioning_device_secrets_start(&flash_state, &lc_ctrl,
                                                      &otp_ctrl, &export_data));
    CHECK_STATUS_OK(ujson_serialize_manuf_provisioning_t(&uj, &export_data));

    // Issue and wait for reset.
    rstmgr_testutils_reason_clear();
    CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));
    wait_for_interrupt();
  } else if (info == kDifRstmgrResetInfoSw) {
    LOG_INFO("provisioning check status");
    CHECK_STATUS_OK(provisioning_device_secrets_end(&otp_ctrl));
  } else {
    LOG_FATAL("Unexpected reset reason: %08x", info);
  }

  return true;
}
