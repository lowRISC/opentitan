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

  /** Key manager secret word size. */
  kSecretWordSize = 8,
};

/**
 * Key manager Creator Secret stored in info flash page.
 */
static const uint32_t kCreatorSecret[kSecretWordSize] = {
    0x4e919d54, 0x322288d8, 0x4bd127c7, 0x9f89bc56,
    0xb4fb0fdf, 0x1ca1567b, 0x13a0e876, 0xa6521d8f};

/**
 * Key manager Owner Secret stored in info flash page.
 */
static const uint32_t kOwnerSecret[kSecretWordSize] = {
    0xa6521d8f, 0x13a0e876, 0x1ca1567b, 0xb4fb0fdf,
    0x9f89bc56, 0x4bd127c7, 0x322288d8, 0x4e919d54,
};

static void write_info_page(dif_flash_ctrl_state_t *flash, uint32_t page_id,
                            const uint32_t *data) {
  uint32_t address = flash_ctrl_testutils_info_region_setup(
      flash, page_id, kFlashInfoBankId, kFlashInfoPartitionId);

  CHECK(flash_ctrl_testutils_erase_and_write_page(
      flash, address, kFlashInfoPartitionId, data,
      kDifFlashCtrlPartitionTypeInfo, kSecretWordSize));

  uint32_t readback_data[kSecretWordSize];
  CHECK(flash_ctrl_testutils_read(flash, address, kFlashInfoPartitionId,
                                  readback_data, kDifFlashCtrlPartitionTypeInfo,
                                  kSecretWordSize, 0));
  CHECK_ARRAYS_EQ(data, readback_data, kSecretWordSize);
}

static void init_flash(void) {
  dif_flash_ctrl_state_t flash;

  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash, mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));

  // Initialize flash secrets.
  write_info_page(&flash, kFlashInfoPageIdCreatorSecret, kCreatorSecret);
  write_info_page(&flash, kFlashInfoPageIdOwnerSecret, kOwnerSecret);
}

void keymgr_testutils_startup(dif_keymgr_t *keymgr, dif_kmac_t *kmac) {
  dif_rstmgr_t rstmgr;
  dif_rstmgr_reset_info_bitfield_t info;

  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));
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

    init_flash();

    // Lock otp secret partition.
    dif_otp_ctrl_t otp;
    CHECK_DIF_OK(dif_otp_ctrl_init(
        mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp));
    otp_ctrl_testutils_lock_partition(&otp, kDifOtpCtrlPartitionSecret2, 0);

    // Reboot device.
    rstmgr_testutils_reason_clear();
    CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));

    // Wait here until device reset.
    wait_for_interrupt();

  } else {
    CHECK(info == kDifRstmgrResetInfoSw, "Unexpected reset reason: %08x", info);
    LOG_INFO(
        "Powered up for the second time, actuate keymgr and perform test.");

    // Initialize KMAC in preparation for keymgr use.
    CHECK_DIF_OK(dif_kmac_init(
        mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), kmac));

    // We shouldn't use the KMAC block's default entropy setting for keymgr, so
    // configure it to use software entropy (and a sideloaded key, although it
    // shouldn't matter here and tests should reconfigure if needed).
    kmac_testutils_config(kmac, true);

    // Initialize keymgr context.
    CHECK_DIF_OK(dif_keymgr_init(
        mmio_region_from_addr(TOP_EARLGREY_KEYMGR_BASE_ADDR), keymgr));

    // Advance to Initialized state.
    keymgr_testutils_check_state(keymgr, kDifKeymgrStateReset);
    keymgr_testutils_advance_state(keymgr, NULL);
    keymgr_testutils_check_state(keymgr, kDifKeymgrStateInitialized);
    LOG_INFO("Keymgr entered Init State");

    // Advance to CreatorRootKey state.
    if (is_using_test_rom) {
      LOG_INFO("Using test_rom, setting inputs and advancing state...");
      keymgr_testutils_advance_state(keymgr, &kCreatorParams);
    } else {
      LOG_INFO("Using rom, only advancing state...");
      CHECK_DIF_OK(dif_keymgr_advance_state_raw(keymgr));
      keymgr_testutils_wait_for_operation_done(keymgr);
    }
    keymgr_testutils_check_state(keymgr, kDifKeymgrStateCreatorRootKey);
    LOG_INFO("Keymgr entered CreatorRootKey State");
  }
}

void keymgr_testutils_advance_state(const dif_keymgr_t *keymgr,
                                    const dif_keymgr_state_params_t *params) {
  CHECK_DIF_OK(dif_keymgr_advance_state(keymgr, params));
  keymgr_testutils_wait_for_operation_done(keymgr);
}

void keymgr_testutils_check_state(const dif_keymgr_t *keymgr,
                                  const dif_keymgr_state_t exp_state) {
  dif_keymgr_state_t act_state;
  CHECK_DIF_OK(dif_keymgr_get_state(keymgr, &act_state));
  CHECK(act_state == exp_state,
        "Keymgr in unexpected state: %x, expected to be %x", act_state,
        exp_state);
}

void keymgr_testutils_generate_identity(const dif_keymgr_t *keymgr) {
  CHECK_DIF_OK(dif_keymgr_generate_identity_seed(keymgr));
  keymgr_testutils_wait_for_operation_done(keymgr);
}

void keymgr_testutils_generate_versioned_key(
    const dif_keymgr_t *keymgr,
    const dif_keymgr_versioned_key_params_t params) {
  CHECK_DIF_OK(dif_keymgr_generate_versioned_key(keymgr, params));
  keymgr_testutils_wait_for_operation_done(keymgr);
}

void keymgr_testutils_disable(const dif_keymgr_t *keymgr) {
  CHECK_DIF_OK(dif_keymgr_disable(keymgr));
  keymgr_testutils_wait_for_operation_done(keymgr);
}

void keymgr_testutils_wait_for_operation_done(const dif_keymgr_t *keymgr) {
  dif_keymgr_status_codes_t status;
  do {
    CHECK_DIF_OK(dif_keymgr_get_status_codes(keymgr, &status));
  } while (status == 0);
  CHECK(status == kDifKeymgrStatusCodeIdle, "Unexpected status: %x", status);
}
