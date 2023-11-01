// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/json/provisioning_data.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/silicon_creator/manuf/lib/personalize.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

static dif_flash_ctrl_state_t flash_ctrl_state;
static dif_lc_ctrl_t lc_ctrl;
static dif_otp_ctrl_t otp_ctrl;
static dif_rstmgr_t rstmgr;

static manuf_perso_data_in_t in_data;
static manuf_perso_data_out_t out_data;

/**
 * Initializes all DIF handles used in this SRAM program.
 */
static status_t peripheral_handles_init(void) {
  TRY(dif_flash_ctrl_init_state(
      &flash_ctrl_state,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
  TRY(dif_lc_ctrl_init(mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_BASE_ADDR),
                       &lc_ctrl));
  TRY(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp_ctrl));
  TRY(dif_rstmgr_init(mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR),
                      &rstmgr));
  return OK_STATUS();
}

/**
 * Perform software reset.
 */
static void sw_reset(void) {
  rstmgr_testutils_reason_clear();
  CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));
  wait_for_interrupt();
}

/**
 * Provision OTP Secret2 partition and keymgr flash info pages (1, 2, and 4).
 */
static status_t personalize(ujson_t *uj) {
  if (!status_ok(manuf_personalize_device_secrets_check(&otp_ctrl))) {
    LOG_INFO("Waiting for FT provisioning data ...");
    TRY(ujson_deserialize_manuf_perso_data_in_t(uj, &in_data));
    TRY(manuf_personalize_device_secrets(&flash_ctrl_state, &lc_ctrl, &otp_ctrl,
                                         &in_data, &out_data));
    LOG_INFO("Exporting FT provisioning data ...");
    RESP_OK(ujson_serialize_manuf_perso_data_out_t, uj, &out_data);
    // We need to reset the chip here to activate the keymgr seeds.
    sw_reset();
  }

  // TODO(#19455): crank keymgr and generate certificates.

  return OK_STATUS();
}

bool test_main(void) {
  CHECK_STATUS_OK(peripheral_handles_init());
  ujson_t uj = ujson_ottf_console();

  CHECK_STATUS_OK(personalize(&uj));

  return true;
}
