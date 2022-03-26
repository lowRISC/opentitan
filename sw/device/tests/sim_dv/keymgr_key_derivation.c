// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_keymgr.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "keymgr_regs.h"  // Generated.
#include "kmac_regs.h"    // Generated.

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
 * Software binding value for advancing to creator state
 */
const struct dif_keymgr_state_params kCreatorParams = {
    .binding_value = {0xdc96c23d, 0xaf36e268, 0xcb68ff71, 0xe92f76e2,
                      0xb8a8379d, 0x426dc745, 0x19f5cff7, 0x4ec9c6d6},
};

/**
 * Software binding value for advancing to owner int state
 */
const struct dif_keymgr_state_params kOwnerIntParams = {
    .binding_value = {0xe4987b39, 0x3f83d390, 0xc2f3bbaf, 0x3195dbfa,
                      0x23fb480c, 0xb012ae5e, 0xf1394d28, 0x1940ceeb},
};

/**
 * Key manager Creator Secret stored in info flash page.
 */
const uint32_t kCreatorSecret[kSecretWordSize] = {
    0x4e919d54, 0x322288d8, 0x4bd127c7, 0x9f89bc56,
    0xb4fb0fdf, 0x1ca1567b, 0x13a0e876, 0xa6521d8f};

/**
 * Key manager Owner Secret stored in info flash page.
 */
const uint32_t kOwnerSecret[kSecretWordSize] = {
    0xa6521d8f, 0x13a0e876, 0x1ca1567b, 0xb4fb0fdf,
    0x9f89bc56, 0x4bd127c7, 0x322288d8, 0x4e919d54,
};

/**
 * Kmac prefix "KMAC" with empty custom string
 */
#define KMAC_PREFIX_SIZE 11
const uint32_t kKmacPrefix[KMAC_PREFIX_SIZE] = {
    0x4d4b2001, 0x00014341, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
};

const test_config_t kTestConfig;

static void write_info_page(dif_flash_ctrl_state_t *flash, uint32_t page_id,
                            const uint32_t *data) {
  uint32_t address = flash_ctrl_testutils_info_region_setup(
      flash, page_id, kFlashInfoBankId, kFlashInfoPartitionId);

  CHECK(flash_ctrl_testutils_erase_and_write_page(
            flash, address, kFlashInfoPartitionId, data,
            kDifFlashCtrlPartitionTypeInfo, kSecretWordSize) == 0);

  uint32_t readback_data[kSecretWordSize];
  CHECK(flash_ctrl_testutils_read_page(
            flash, address, kFlashInfoPartitionId, readback_data,
            kDifFlashCtrlPartitionTypeInfo, kSecretWordSize, 0) == 0);
  CHECK_BUFFER(data, readback_data, kSecretWordSize);
}

static void init_flash(void) {
  dif_flash_ctrl_state_t flash;

  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash, mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));

  // Initialize flash secrets.
  write_info_page(&flash, kFlashInfoPageIdCreatorSecret, kCreatorSecret);
  write_info_page(&flash, kFlashInfoPageIdOwnerSecret, kOwnerSecret);
}

/** Place kmac into sideload mode for correct keymgr operation */
static void init_kmac_for_keymgr(void) {
  dif_kmac_t kmac;
  CHECK_DIF_OK(
      dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), &kmac));

  // Configure KMAC hardware using software entropy.
  dif_kmac_config_t config = (dif_kmac_config_t){
      .sideload = true,
  };
  CHECK_DIF_OK(dif_kmac_configure(&kmac, config));

  for (uint8_t i = 0; i < KMAC_PREFIX_SIZE; ++i) {
    mmio_region_write32(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR),
                        KMAC_PREFIX_0_REG_OFFSET + i * 4, kKmacPrefix[i]);
  }
}

void keymgr_advance_state(const dif_keymgr_t *keymgr,
                          const dif_keymgr_state_params_t *params) {
  CHECK_DIF_OK(dif_keymgr_advance_state(keymgr, params));

  while (true) {
    dif_keymgr_status_codes_t status;

    CHECK_DIF_OK(dif_keymgr_get_status_codes(keymgr, &status));
    if (status == 0) {
      LOG_INFO("Advancing to next state");
    } else if (status == kDifKeymgrStatusCodeIdle) {
      break;
    } else {
      LOG_ERROR("Unexpected status: %0x", status);
      break;
    }
  }
}

void keymgr_check_state(const dif_keymgr_t *keymgr,
                        const dif_keymgr_state_t exp_state) {
  dif_keymgr_state_t act_state;
  CHECK_DIF_OK(dif_keymgr_get_state(keymgr, &act_state));
  if (act_state != exp_state) {
    LOG_INFO("Keymgr in unexpected state: %0x, expected to be %0x", act_state,
             exp_state);
  }
}

bool test_main(void) {
  dif_rstmgr_t rstmgr;
  dif_rstmgr_reset_info_bitfield_t info;

  // Initialize pwrmgr
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));
  CHECK_DIF_OK(dif_rstmgr_reset_info_get(&rstmgr, &info));

  // POR reset
  if (info == kDifRstmgrResetInfoPor) {
    LOG_INFO("Powered up for the first time, program flash");

    // Initialize flash
    init_flash();

    // Lock otp secret partition
    dif_otp_ctrl_t otp;
    CHECK_DIF_OK(dif_otp_ctrl_init(
        mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp));
    otp_ctrl_testutils_lock_partition(&otp, kDifOtpCtrlPartitionSecret2, 0);

    // reboot device
    CHECK_DIF_OK(dif_rstmgr_reset_info_clear(&rstmgr));
    CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));

    // wait here until device reset
    wait_for_interrupt();

  } else if (info == kDifRstmgrResetInfoSw) {
    LOG_INFO("Powered up for the second time, actuate keymgr");

    init_kmac_for_keymgr();

    dif_keymgr_t keymgr;
    CHECK_DIF_OK(dif_keymgr_init(
        mmio_region_from_addr(TOP_EARLGREY_KEYMGR_BASE_ADDR), &keymgr));

    keymgr_check_state(&keymgr, kDifKeymgrStateReset);

    keymgr_advance_state(&keymgr, NULL);
    keymgr_check_state(&keymgr, kDifKeymgrStateInitialized);
    LOG_INFO("Keymgr entered Init State");

    keymgr_advance_state(&keymgr, &kCreatorParams);
    keymgr_check_state(&keymgr, kDifKeymgrStateCreatorRootKey);
    LOG_INFO("Keymgr entered CreatorRootKey State");

    keymgr_advance_state(&keymgr, &kOwnerIntParams);
    keymgr_check_state(&keymgr, kDifKeymgrStateOwnerIntermediateKey);
    LOG_INFO("Keymgr entered OwnerIntKey State");

    CHECK_DIF_OK(dif_keymgr_generate_identity_seed(&keymgr));
    LOG_INFO("Keymgr generated identity");

    return true;
  } else {
    LOG_FATAL("Unexpected reset reason unexpected: %0x", info);
  }

  return false;
}
