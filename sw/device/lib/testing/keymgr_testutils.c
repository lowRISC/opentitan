// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/keymgr_testutils.h"

#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_keymgr.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/kmac_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/silicon_creator/lib/base/chip.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

enum {
  /** Flash Secret partition ID. */
  kFlashInfoPartitionId = 0,

  /** Secret partition flash bank ID. */
  kFlashInfoBankId = 0,

  /** Creator Secret flash info page ID. */
  kFlashInfoPageIdCreatorSecret = 1,

  /** Owner Secret flash info page ID. */
  kFlashInfoPageIdOwnerSecret = 2,
};

static status_t write_info_page(dif_flash_ctrl_state_t *flash, uint32_t page_id,
                                const keymgr_testutils_secret_t *data,
                                bool scramble) {
  uint32_t address = 0;
  if (scramble) {
    TRY(flash_ctrl_testutils_info_region_scrambled_setup(
        flash, page_id, kFlashInfoBankId, kFlashInfoPartitionId, &address));
  } else {
    TRY(flash_ctrl_testutils_info_region_setup(
        flash, page_id, kFlashInfoBankId, kFlashInfoPartitionId, &address));
  }

  TRY(flash_ctrl_testutils_erase_and_write_page(
      flash, address, kFlashInfoPartitionId, data->value,
      kDifFlashCtrlPartitionTypeInfo, ARRAYSIZE(data->value)));

  keymgr_testutils_secret_t readback_data;
  TRY(flash_ctrl_testutils_read(
      flash, address, kFlashInfoPartitionId, readback_data.value,
      kDifFlashCtrlPartitionTypeInfo, ARRAYSIZE(readback_data.value), 0));
  TRY_CHECK(memcmp(data->value, readback_data.value, sizeof(data->value)) == 0);
  return OK_STATUS();
}

status_t keymgr_testutils_flash_init(
    dif_flash_ctrl_state_t *flash,
    const keymgr_testutils_secret_t *creator_secret,
    const keymgr_testutils_secret_t *owner_secret) {
  // Initialize flash secrets.
  write_info_page(flash, kFlashInfoPageIdCreatorSecret, creator_secret,
                  /*scramble=*/true);
  write_info_page(flash, kFlashInfoPageIdOwnerSecret, owner_secret,
                  /*scramble=*/true);
  return OK_STATUS();
}

status_t keymgr_testutils_startup(dif_keymgr_t *keymgr, dif_kmac_t *kmac) {
  dif_flash_ctrl_state_t flash;
  dif_rstmgr_t rstmgr;
  dif_rstmgr_reset_info_bitfield_t info;

  TRY(dif_rstmgr_init(mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR),
                      &rstmgr));
  info = rstmgr_testutils_reason_get();

  // Check the last word of the retention SRAM creator area to determine the
  // type of the ROM.
  bool is_using_test_rom =
      retention_sram_get()
          ->reserved_creator[ARRAYSIZE((retention_sram_t){0}.reserved_creator) -
                             1] == TEST_ROM_IDENTIFIER;

  // POR reset.
  if (info == kDifRstmgrResetInfoPor) {
    LOG_INFO("Powered up for the first time, program flash");

    TRY(dif_flash_ctrl_init_state(
        &flash, mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));

    TRY(keymgr_testutils_flash_init(&flash, &kCreatorSecret, &kOwnerSecret));

    // Lock otp secret partition.
    dif_otp_ctrl_t otp;
    TRY(dif_otp_ctrl_init(
        mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp));
    TRY(otp_ctrl_testutils_lock_partition(&otp, kDifOtpCtrlPartitionSecret2,
                                          0));

    // Reboot device.
    rstmgr_testutils_reason_clear();
    TRY(dif_rstmgr_software_device_reset(&rstmgr));

    // Wait here until device reset.
    wait_for_interrupt();

  } else {
    TRY_CHECK(info == kDifRstmgrResetInfoSw, "Unexpected reset reason: %08x",
              info);
    LOG_INFO(
        "Powered up for the second time, actuate keymgr and perform test.");

    // Initialize KMAC in preparation for keymgr use.
    TRY(dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR),
                      kmac));

    // We shouldn't use the KMAC block's default entropy setting for keymgr, so
    // configure it to use software entropy (and a sideloaded key, although it
    // shouldn't matter here and tests should reconfigure if needed).
    TRY(kmac_testutils_config(kmac, true));

    // Initialize keymgr context.
    TRY(dif_keymgr_init(mmio_region_from_addr(TOP_EARLGREY_KEYMGR_BASE_ADDR),
                        keymgr));

    // Advance to Initialized state.
    TRY(keymgr_testutils_check_state(keymgr, kDifKeymgrStateReset));
    TRY(keymgr_testutils_advance_state(keymgr, NULL));
    TRY(keymgr_testutils_check_state(keymgr, kDifKeymgrStateInitialized));
    LOG_INFO("Keymgr entered Init State");

    // Advance to CreatorRootKey state.
    if (is_using_test_rom) {
      LOG_INFO("Using test_rom, setting inputs and advancing state...");
      TRY(keymgr_testutils_advance_state(keymgr, &kCreatorParams));
    } else {
      LOG_INFO("Using rom, only advancing state...");
      TRY(dif_keymgr_advance_state_raw(keymgr));
      TRY(keymgr_testutils_wait_for_operation_done(keymgr));
    }
    TRY(keymgr_testutils_check_state(keymgr, kDifKeymgrStateCreatorRootKey));
    LOG_INFO("Keymgr entered CreatorRootKey State");

    // Identity generation is not really necessary for all tests, but it is
    // added to make sure each test using this function is also compatible with
    // the DV_WAIT sequences from keymgr_key_derivation vseq
    TRY(keymgr_testutils_generate_identity(keymgr));
    LOG_INFO("Keymgr generated identity at CreatorRootKey State");
  }
  return OK_STATUS();
}

status_t keymgr_testutils_advance_state(
    const dif_keymgr_t *keymgr, const dif_keymgr_state_params_t *params) {
  TRY(dif_keymgr_advance_state(keymgr, params));
  return keymgr_testutils_wait_for_operation_done(keymgr);
}

status_t keymgr_testutils_check_state(const dif_keymgr_t *keymgr,
                                      const dif_keymgr_state_t exp_state) {
  dif_keymgr_state_t act_state;
  TRY(dif_keymgr_get_state(keymgr, &act_state));
  TRY_CHECK(act_state == exp_state,
            "Keymgr in unexpected state: %x, expected to be %x", act_state,
            exp_state);
  return OK_STATUS();
}

status_t keymgr_testutils_generate_identity(const dif_keymgr_t *keymgr) {
  TRY(dif_keymgr_generate_identity_seed(keymgr));
  return keymgr_testutils_wait_for_operation_done(keymgr);
}

status_t keymgr_testutils_generate_versioned_key(
    const dif_keymgr_t *keymgr,
    const dif_keymgr_versioned_key_params_t params) {
  TRY(dif_keymgr_generate_versioned_key(keymgr, params));
  return keymgr_testutils_wait_for_operation_done(keymgr);
}

status_t keymgr_testutils_disable(const dif_keymgr_t *keymgr) {
  TRY(dif_keymgr_disable(keymgr));
  return keymgr_testutils_wait_for_operation_done(keymgr);
}

status_t keymgr_testutils_wait_for_operation_done(const dif_keymgr_t *keymgr) {
  dif_keymgr_status_codes_t status;
  do {
    TRY(dif_keymgr_get_status_codes(keymgr, &status));
  } while (status == 0);
  TRY_CHECK(status == kDifKeymgrStatusCodeIdle, "Unexpected status: %x",
            status);
  return OK_STATUS();
}
