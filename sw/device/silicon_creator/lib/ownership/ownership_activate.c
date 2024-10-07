// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/ownership/ownership_activate.h"

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_msg.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/ownership/owner_block.h"
#include "sw/device/silicon_creator/lib/ownership/ownership_key.h"

rom_error_t ownership_activate(boot_data_t *bootdata,
                               hardened_bool_t write_both_pages) {
  // Check if page1 parses correctly.
  owner_config_t config;
  owner_application_keyring_t keyring;
  HARDENED_RETURN_IF_ERROR(
      owner_block_parse(&owner_page[1], &config, &keyring));

  // Seal page one to this chip.
  ownership_seal_page(/*page=*/1);

  // If requested, reset the mim security version of the application firmware.
  if (owner_page[1].min_security_version_bl0 != UINT32_MAX) {
    bootdata->min_security_version_bl0 = owner_page[1].min_security_version_bl0;
  }

  // TODO(cfrantz): Consider reading back the flash pages to check that the
  // flash writes succeeded.
  //
  // Program the sealed page into slot 1.
  HARDENED_RETURN_IF_ERROR(flash_ctrl_info_erase(&kFlashCtrlInfoPageOwnerSlot1,
                                                 kFlashCtrlEraseTypePage));
  HARDENED_RETURN_IF_ERROR(flash_ctrl_info_write(
      &kFlashCtrlInfoPageOwnerSlot1, 0,
      sizeof(owner_page[1]) / sizeof(uint32_t), &owner_page[1]));

  if (write_both_pages == kHardenedBoolTrue) {
    // Program the same data into slot 0.
    HARDENED_RETURN_IF_ERROR(flash_ctrl_info_erase(
        &kFlashCtrlInfoPageOwnerSlot0, kFlashCtrlEraseTypePage));
    HARDENED_RETURN_IF_ERROR(flash_ctrl_info_write(
        &kFlashCtrlInfoPageOwnerSlot0, 0,
        sizeof(owner_page[1]) / sizeof(uint32_t), &owner_page[1]));
  }

  return kErrorOk;
}

static rom_error_t activate_handler(boot_svc_msg_t *msg,
                                    boot_data_t *bootdata) {
  // Check if page1 is in a valid state for a transfer (e.g. signature and owner
  // requirements are met). We do this first (rather than parse) because if the
  // signature requirements are not met, the RAM copy of the owner page will be
  // destroyed.
  if (owner_block_page1_valid_for_transfer(bootdata) != kHardenedBoolTrue) {
    return kErrorOwnershipInvalidInfoPage;
  }

  // Check the activation key and the nonce.
  size_t len = (uintptr_t)&msg->ownership_activate_req.signature -
               (uintptr_t)&msg->ownership_activate_req.primary_bl0_slot;
  if (ownership_key_validate(/*page=*/1, kOwnershipKeyActivate,
                             &msg->ownership_activate_req.signature,
                             &msg->ownership_activate_req.primary_bl0_slot,
                             len) == kHardenedBoolFalse) {
    return kErrorOwnershipInvalidSignature;
  }
  if (!nonce_equal(&msg->ownership_activate_req.nonce, &bootdata->nonce)) {
    return kErrorOwnershipInvalidNonce;
  }

  // Verify the device identification number is correct.
  lifecycle_device_id_t device_id;
  lifecycle_device_id_get(&device_id);
  if (lifecycle_din_eq(&device_id, msg->ownership_activate_req.din) !=
      kHardenedBoolTrue) {
    return kErrorOwnershipInvalidDin;
  }

  HARDENED_RETURN_IF_ERROR(
      ownership_activate(bootdata, /*write_both_pages=*/kHardenedBoolTrue));

  // The requested primary_bl0_slot is user input.  Validate and clamp it to
  // legal values.
  if (msg->ownership_activate_req.primary_bl0_slot == kBootSlotB) {
    bootdata->primary_bl0_slot = kBootSlotB;
  } else {
    bootdata->primary_bl0_slot = kBootSlotA;
  }

  // Set the ownership state to LockedOwner.
  nonce_new(&bootdata->nonce);
  bootdata->ownership_state = kOwnershipStateLockedOwner;
  bootdata->ownership_transfers += 1;
  memset(bootdata->next_owner, 0, sizeof(bootdata->next_owner));
  return kErrorWriteBootdataThenReboot;
}

rom_error_t ownership_activate_handler(boot_svc_msg_t *msg,
                                       boot_data_t *bootdata) {
  rom_error_t error = kErrorOwnershipInvalidState;
  switch (bootdata->ownership_state) {
    case kOwnershipStateUnlockedSelf:
    case kOwnershipStateUnlockedAny:
    case kOwnershipStateUnlockedEndorsed:
      error = activate_handler(msg, bootdata);
      break;
    default:
        /* nothing */;
  }
  boot_svc_ownership_activate_res_init(
      error == kErrorWriteBootdataThenReboot ? kErrorOk : error,
      &msg->ownership_activate_res);
  return error;
}
