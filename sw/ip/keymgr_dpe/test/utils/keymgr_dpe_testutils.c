// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/ip/keymgr_dpe/test/utils/keymgr_dpe_testutils.h"

#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/ip/flash_ctrl/dif/dif_flash_ctrl.h"
#include "sw/ip/flash_ctrl/driver/flash_ctrl.h"
#include "sw/ip/flash_ctrl/test/utils/flash_ctrl_testutils.h"
#include "sw/ip/keymgr_dpe/dif/dif_keymgr_dpe.h"
#include "sw/ip/keymgr_dpe/driver/keymgr_dpe.h"
#include "sw/ip/otp_ctrl/dif/dif_otp_ctrl.h"
#include "sw/ip/otp_ctrl/driver/otp_ctrl.h"
#include "sw/ip/otp_ctrl/test/utils/otp_ctrl_testutils.h"
#include "sw/ip/rstmgr/dif/dif_rstmgr.h"
#include "sw/ip/rstmgr/driver/rstmgr.h"
#include "sw/ip/rstmgr/test/utils/rstmgr_testutils.h"
#include "sw/lib/sw/device/runtime/ibex.h"
#include "sw/lib/sw/device/runtime/log.h"
#include "sw/lib/sw/device/silicon_creator/base/chip.h"

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
                                const keymgr_dpe_testutils_secret_t *data,
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

  keymgr_dpe_testutils_secret_t readback_data;
  TRY(flash_ctrl_testutils_read(
      flash, address, kFlashInfoPartitionId, readback_data.value,
      kDifFlashCtrlPartitionTypeInfo, ARRAYSIZE(readback_data.value), 0));
  TRY_CHECK(memcmp(data->value, readback_data.value, sizeof(data->value)) == 0);
  return OK_STATUS();
}

status_t keymgr_dpe_testutils_flash_init(
    dif_flash_ctrl_state_t *flash,
    const keymgr_dpe_testutils_secret_t *creator_secret,
    const keymgr_dpe_testutils_secret_t *owner_secret) {
  // Initialize flash secrets.
  write_info_page(flash, kFlashInfoPageIdCreatorSecret, creator_secret,
                  /*scramble=*/true);
  write_info_page(flash, kFlashInfoPageIdOwnerSecret, owner_secret,
                  /*scramble=*/true);
  return OK_STATUS();
}

status_t keymgr_dpe_testutils_startup(dif_keymgr_dpe_t *keymgr_dpe) {
  dif_flash_ctrl_state_t flash;
  dif_rstmgr_t rstmgr;
  dif_rstmgr_reset_info_bitfield_t info;

  TRY(dif_rstmgr_init(mmio_region_from_addr(kRstmgrAonBaseAddr[0]), &rstmgr));
  info = rstmgr_testutils_reason_get();

  // POR reset.
  if (info == kDifRstmgrResetInfoPor) {
    LOG_INFO("Powered up for the first time, program flash");

    TRY(dif_flash_ctrl_init_state(
        &flash, mmio_region_from_addr(kFlashCtrlCoreBaseAddr[0])));

    TRY(keymgr_dpe_testutils_flash_init(&flash, &kCreatorSecret,
                                        &kOwnerSecret));

    // Lock otp secret partition.
    dif_otp_ctrl_t otp;
    TRY(dif_otp_ctrl_init(mmio_region_from_addr(kOtpCtrlCoreBaseAddr[0]),
                          &otp));
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
        "Powered up for the second time, actuate keymgr_dpe and perform test.");

    // Initialize keymgr_dpe context.
    TRY(dif_keymgr_dpe_init(mmio_region_from_addr(kKeymgrDpeBaseAddr[0]),
                            keymgr_dpe));

    // Advance to Initialized state.
    TRY(keymgr_dpe_testutils_check_state(keymgr_dpe, kDifKeymgrDpeStateReset));
    TRY(dif_keymgr_dpe_initialize(keymgr_dpe, /*slot_dst_sel=*/1));
    TRY(keymgr_dpe_testutils_wait_for_operation_done(keymgr_dpe));
    TRY(keymgr_dpe_testutils_check_state(keymgr_dpe,
                                         kDifKeymgrDpeStateAvailable));
    LOG_INFO("UDS is latched.");
  }
  return OK_STATUS();
}

status_t keymgr_dpe_testutils_advance_state(
    const dif_keymgr_dpe_t *keymgr_dpe,
    const dif_keymgr_dpe_advance_params_t *params) {
  TRY(dif_keymgr_dpe_advance_state(keymgr_dpe, params));
  return keymgr_dpe_testutils_wait_for_operation_done(keymgr_dpe);
}

status_t keymgr_dpe_testutils_erase_slot(
    const dif_keymgr_dpe_t *keymgr_dpe,
    const dif_keymgr_dpe_erase_params_t *params) {
  TRY(dif_keymgr_dpe_erase_slot(keymgr_dpe, params));
  return keymgr_dpe_testutils_wait_for_operation_done(keymgr_dpe);
}

status_t keymgr_dpe_testutils_generate(
    const dif_keymgr_dpe_t *keymgr_dpe,
    const dif_keymgr_dpe_generate_params_t *params,
    dif_keymgr_dpe_output_t *key) {
  TRY(dif_keymgr_dpe_generate(keymgr_dpe, params));
  TRY(keymgr_dpe_testutils_wait_for_operation_done(keymgr_dpe));
  TRY(dif_keymgr_read_output(keymgr_dpe, key));
  return OK_STATUS();
}

status_t keymgr_dpe_testutils_check_state(
    const dif_keymgr_dpe_t *keymgr_dpe,
    const dif_keymgr_dpe_state_t exp_state) {
  dif_keymgr_dpe_state_t act_state;
  TRY(dif_keymgr_dpe_get_state(keymgr_dpe, &act_state));
  TRY_CHECK(act_state == exp_state,
            "KeymgrDPE in unexpected state: %x, expected to be %x", act_state,
            exp_state);
  return OK_STATUS();
}

status_t keymgr_dpe_testutils_wait_for_operation_done(
    const dif_keymgr_dpe_t *keymgr_dpe) {
  dif_keymgr_dpe_status_codes_t status;
  do {
    TRY(dif_keymgr_dpe_get_status_codes(keymgr_dpe, &status));
  } while (status == 0);
  TRY_CHECK(status == kDifKeymgrDpeStatusCodeIdle, "Unexpected status: %x",
            status);
  return OK_STATUS();
}
