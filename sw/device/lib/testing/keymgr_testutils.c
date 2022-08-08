// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/keymgr_testutils.h"

#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_keymgr.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"

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

void keymgr_testutils_init_flash(void) {
  dif_flash_ctrl_state_t flash;

  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash, mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));

  // Initialize flash secrets.
  write_info_page(&flash, kFlashInfoPageIdCreatorSecret, kCreatorSecret);
  write_info_page(&flash, kFlashInfoPageIdOwnerSecret, kOwnerSecret);
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
