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
#include "sw/device/lib/testing/lc_ctrl_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/silicon_creator/manuf/lib/individualize_sw_cfg.h"
#include "sw/device/silicon_creator/manuf/lib/personalize.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

static dif_flash_ctrl_state_t flash_ctrl_state;
static dif_lc_ctrl_t lc_ctrl;
static dif_otp_ctrl_t otp_ctrl;
static dif_rstmgr_t rstmgr;

static ecc_p256_public_key_t host_ecc_pk;
static wrapped_rma_unlock_token_t wrapped_rma_token;

/**
 * Initializes all DIF handles used in this program.
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
 * Issue a software reset.
 */
static void sw_reset(void) {
  rstmgr_testutils_reason_clear();
  CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));
  wait_for_interrupt();
}

/**
 * Provision OTP SECRET{1,2} partitions, enable flash scrambling, and reboot.
 */
static status_t personalize_otp_secrets(ujson_t *uj) {
  // Provision OTP Secret1 partition, and complete provisioning of OTP
  // CreatorSwCfg partition.
  if (!status_ok(manuf_personalize_device_secret1_check(&otp_ctrl))) {
    TRY(manuf_personalize_device_secret1(&lc_ctrl, &otp_ctrl));
  }
  if (!status_ok(manuf_individualize_device_creator_sw_cfg_check(&otp_ctrl))) {
    TRY(manuf_individualize_device_flash_data_default_cfg(&otp_ctrl));
    TRY(manuf_individualize_device_creator_sw_cfg_lock(&otp_ctrl));
    LOG_INFO("Bootstrap requested.");
    wait_for_interrupt();
  }

  // Provision OTP Secret2 partition and keymgr flash info pages (1, 2, and 4).
  if (!status_ok(manuf_personalize_device_secrets_check(&otp_ctrl))) {
    LOG_INFO("Waiting for host public key ...");
    TRY(ujson_deserialize_ecc_p256_public_key_t(uj, &host_ecc_pk));
    TRY(manuf_personalize_device_secrets(&flash_ctrl_state, &lc_ctrl, &otp_ctrl,
                                         &host_ecc_pk, &wrapped_rma_token));
    LOG_INFO("Exporting RMA token ...");
    RESP_OK(ujson_serialize_wrapped_rma_unlock_token_t, uj, &wrapped_rma_token);
    sw_reset();
  }

  return OK_STATUS();
}

bool test_main(void) {
  CHECK_STATUS_OK(peripheral_handles_init());
  ujson_t uj = ujson_ottf_console();
  CHECK_STATUS_OK(lc_ctrl_testutils_operational_state_check(&lc_ctrl));
  CHECK_STATUS_OK(personalize_otp_secrets(&uj));
  return true;
}
