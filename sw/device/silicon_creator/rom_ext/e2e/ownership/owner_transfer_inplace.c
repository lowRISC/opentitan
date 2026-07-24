// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_msg.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_next_boot_bl0_slot.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/lib/ownership/datatypes.h"
#include "sw/device/silicon_creator/rom_ext/rom_ext_boot_policy_ptrs.h"

OTTF_DEFINE_TEST_CONFIG();

/**
 * Performs an in-place ownership transfer *without* unlocking the device.
 *
 * This mode of transfer is only supported when the active owner block (Page 0)
 * update mode is set to `AnyVersion`. When in this mode, the device firmware
 * can directly write the new owner block to flash info Page 1 without executing
 * the unlock/lock state-transition protocol.
 */
static status_t trigger_inplace_transfer(void) {
  LOG_INFO("Slot A firmware started: Locating Slot B manifest...");
  boot_data_t boot_data = {
      .identifier = kBootDataIdentifier,
  };
  const manifest_t *manifest_b = rom_ext_boot_policy_manifest_b_get();

  LOG_INFO("Reading owner_transfer_blob extension...");
  const manifest_ext_owner_transfer_blob_t *blob = NULL;
  rom_error_t err = manifest_ext_get_owner_transfer_blob(manifest_b, &blob);
  if (err != kErrorOk) {
    LOG_ERROR("Failed to read owner_transfer_blob extension: %r", err);
    return UNKNOWN();
  }

  LOG_INFO("Checking current owner block update mode...");
  flash_ctrl_perms_t read_perm = {
      .read = kMultiBitBool4True,
      .write = kMultiBitBool4False,
      .erase = kMultiBitBool4False,
  };
  flash_ctrl_info_perms_set(&kFlashCtrlInfoPageOwnerSlot0, read_perm);
  owner_block_t current_owner;
  TRY(flash_ctrl_info_read(&kFlashCtrlInfoPageOwnerSlot0, 0,
                           sizeof(owner_block_t) / sizeof(uint32_t),
                           &current_owner));
  LOG_INFO("Current owner update mode: 0x%08x", current_owner.update_mode);
  if (current_owner.update_mode != kOwnershipUpdateModeAnyVersion) {
    LOG_ERROR("Unsupported update mode for transfer: 0x%08x",
              current_owner.update_mode);
    return UNKNOWN();
  }

  LOG_INFO("Configuring flash info page 1 write permissions...");
  flash_ctrl_perms_t perm = {
      .read = kMultiBitBool4True,
      .write = kMultiBitBool4True,
      .erase = kMultiBitBool4True,
  };
  flash_ctrl_info_perms_set(&kFlashCtrlInfoPageOwnerSlot1, perm);

  LOG_INFO("Erasing flash info page 1...");
  TRY(flash_ctrl_info_erase(&kFlashCtrlInfoPageOwnerSlot1,
                            kFlashCtrlEraseTypePage));

  LOG_INFO("Writing new owner block to flash info page 1...");
  TRY(flash_ctrl_info_write(&kFlashCtrlInfoPageOwnerSlot1, 0,
                            sizeof(blob->owner_block) / sizeof(uint32_t),
                            blob->owner_block));

  LOG_INFO("Setting next boot slot to Slot B...");
  retention_sram_t *retram = retention_sram_get();
  boot_svc_msg_t msg = {0};
  boot_svc_next_boot_bl0_slot_req_init(kBootSlotB, kBootSlotB,
                                       &msg.next_boot_bl0_slot_req);
  retram->creator.boot_svc_msg = msg;

  LOG_INFO("Triggering system reset to finalize owner transfer...");
  rstmgr_reset();

  return INTERNAL();  // Should not be reached.
}

bool test_main(void) {
  status_t sts = trigger_inplace_transfer();
  if (status_err(sts)) {
    LOG_ERROR("trigger_inplace_transfer failed: %r", sts);
  }
  return false;
}
