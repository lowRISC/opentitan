// Copyright lowRISC contributors (OpenTitan project).
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
#include "sw/device/silicon_creator/lib/attestation.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"
#include "sw/device/silicon_creator/manuf/lib/personalize.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

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

/**
 * Perform software reset.
 */
static void sw_reset(void) {
  rstmgr_testutils_reason_clear();
  CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));
  wait_for_interrupt();
}

static status_t check_array_non_zero(uint32_t *array, size_t num_words) {
  for (size_t i = 0; i < num_words; ++i) {
    if (array[i] == 0) {
      return INTERNAL();
    }
  }
  return OK_STATUS();
}

bool test_main(void) {
  ujson_t uj = ujson_ottf_console();
  CHECK_STATUS_OK(peripheral_handles_init());

  // If we are in the RMA state, this means that the personalization is complete
  // and that the host has issued an LC transition to the RMA state. To allow
  // the host to connect over JTAG and check that we have indeed reached this
  // state, just spin to prevent a reboot.
  dif_lc_ctrl_state_t lc_state = kDifLcCtrlStateInvalid;
  CHECK_DIF_OK(dif_lc_ctrl_get_state(&lc_ctrl, &lc_state));
  if (lc_state == kDifLcCtrlStateRma) {
    LOG_INFO("Now in RMA state, spinning for host to connect over JTAG.");
    // Wait in a loop so that OpenOCD can connect to the TAP without the ROM
    // resetting the chip.
    // Abort simply forever loops on a wait_for_interrupt.
    abort();
  }

  dif_rstmgr_reset_info_bitfield_t info = rstmgr_testutils_reason_get();
  if (info & kDifRstmgrResetInfoPor) {
    // Provision the OTP SECRET1 partition.
    if (!status_ok(manuf_personalize_device_secret1_check(&otp_ctrl))) {
      LOG_INFO("Provisioning OTP SECRET1 ...");
      CHECK_STATUS_OK(manuf_personalize_device_secret1(&lc_ctrl, &otp_ctrl));
      // Wait in a loop so that the test harness can trigger a second bootstrap
      // operation. This is required because the flash scrambling setting may
      // have changed in OTP.
      // The following log message is polled in the host side of this test.
      LOG_INFO("Provisioning OTP SECRET1 Done ...");
      abort();
    }

    // Provision the OTP SECRET2 partition and flash info pages.
    if (!status_ok(manuf_personalize_device_secrets_check(&otp_ctrl))) {
      lc_token_hash_t token_hash;
      // Wait for host the host generated RMA unlock token hash to arrive over
      // the console.
      LOG_INFO("Waiting For RMA Unlock Token Hash ...");

      CHECK_STATUS_OK(
          UJSON_WITH_CRC(ujson_deserialize_lc_token_hash_t, &uj, &token_hash));

      // Perform OTP and flash info writes.
      CHECK_STATUS_OK(manuf_personalize_device_secrets(&flash_state, &lc_ctrl,
                                                       &otp_ctrl, &token_hash));
      LOG_INFO("Provisioning flash info asymmetric keygen seeds ...");
      CHECK_STATUS_OK(manuf_personalize_flash_asymm_key_seed(
          &flash_state, kFlashInfoFieldUdsAttestationKeySeed,
          kAttestationSeedWords));
      CHECK_STATUS_OK(manuf_personalize_flash_asymm_key_seed(
          &flash_state, kFlashInfoFieldCdi0AttestationKeySeed,
          kAttestationSeedWords));
      CHECK_STATUS_OK(manuf_personalize_flash_asymm_key_seed(
          &flash_state, kFlashInfoFieldCdi1AttestationKeySeed,
          kAttestationSeedWords));

      // Read the attestation key seed fields to ensure they are non-zero.
      uint32_t uds_attestation_key_seed[kAttestationSeedWords];
      uint32_t cdi_0_attestation_key_seed[kAttestationSeedWords];
      uint32_t cdi_1_attestation_key_seed[kAttestationSeedWords];
      CHECK_STATUS_OK(manuf_flash_info_field_read(
          &flash_state, kFlashInfoFieldUdsAttestationKeySeed,
          uds_attestation_key_seed, kAttestationSeedWords));
      CHECK_STATUS_OK(check_array_non_zero(uds_attestation_key_seed,
                                           kAttestationSeedWords));
      CHECK_STATUS_OK(manuf_flash_info_field_read(
          &flash_state, kFlashInfoFieldCdi0AttestationKeySeed,
          cdi_0_attestation_key_seed, kAttestationSeedWords));
      CHECK_STATUS_OK(check_array_non_zero(cdi_0_attestation_key_seed,
                                           kAttestationSeedWords));
      CHECK_STATUS_OK(manuf_flash_info_field_read(
          &flash_state, kFlashInfoFieldCdi1AttestationKeySeed,
          cdi_1_attestation_key_seed, kAttestationSeedWords));
      CHECK_STATUS_OK(check_array_non_zero(cdi_1_attestation_key_seed,
                                           kAttestationSeedWords));
      LOG_INFO(
          "Finished provisioning OTP SECRET2 and keymgr flash info pages ...");

      // Reset the chip to activate the OTP partitions and flash pages.
      sw_reset();
    }
  } else if (info == kDifRstmgrResetInfoSw) {
    // Wait in a loop so that OpenOCD can connect to the TAP without the ROM
    // resetting the chip.
    LOG_INFO("Spinning for host to connect over JTAG.");
    abort();
  } else {
    LOG_FATAL("Unexpected reset reason: %08x", info);
  }

  return true;
}
