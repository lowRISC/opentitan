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
#include "sw/device/silicon_creator/lib/sigverify/flash_exec.h"

rom_error_t ownership_activate(boot_data_t *bootdata,
                               hardened_bool_t write_both_pages) {
  // Check if page1 parses correctly.
  HARDENED_RETURN_IF_ERROR(owner_block_parse(
      &owner_page[1], /*check_only*/ kHardenedBoolTrue, NULL, NULL));

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

  // Set the variable checking whether the correct signatures have been
  // verified.
  uint32_t flash_exec = 0;

  // Check the activation key and the nonce.
  size_t len = (uintptr_t)&msg->ownership_activate_req.signature -
               (uintptr_t)&msg->ownership_activate_req.primary_bl0_slot;
  HARDENED_RETURN_IF_ERROR(ownership_key_validate(
      /*page=*/1, kOwnershipKeyActivate, msg->header.type, &bootdata->nonce,
      &msg->ownership_activate_req.signature,
      &msg->ownership_activate_req.primary_bl0_slot, len, &flash_exec));

  // Verify that we passed signature verification for the message.
  HARDENED_CHECK_EQ(flash_exec, kSigverifyFlashExec);

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

  // Copy the prior owner's key so we can save it in the key history.
  uint32_t prior_key_alg = owner_page[0].ownership_key_alg;
  owner_keydata_t prior_owner_key = owner_page[0].owner_key;

  HARDENED_RETURN_IF_ERROR(
      ownership_activate(bootdata, /*write_both_pages=*/kHardenedBoolTrue));

  // The requested primary_bl0_slot is user input.
  // Legal values change the primary boot slot.  All other values result in no
  // change.
  if (msg->ownership_activate_req.primary_bl0_slot == kBootSlotA ||
      msg->ownership_activate_req.primary_bl0_slot == kBootSlotB) {
    bootdata->primary_bl0_slot = msg->ownership_activate_req.primary_bl0_slot;
  }

  if (launder32(bootdata->ownership_state) == kOwnershipStateUnlockedSelf) {
    // An activate from UnlockedSelf is not a transfer and should not
    // regenerate the OwnerSecret page.
    HARDENED_CHECK_EQ(bootdata->ownership_state, kOwnershipStateUnlockedSelf);
  } else {
    // All other activations are transfers and need to regenerate entropy stored
    // in the OwnerSecret page.
    HARDENED_RETURN_IF_ERROR(
        ownership_secret_new(prior_key_alg, &prior_owner_key));
    bootdata->ownership_transfers += 1;
  }

  // Set the ownership state to LockedOwner.
  nonce_new(&bootdata->nonce);
  bootdata->ownership_state = kOwnershipStateLockedOwner;
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
