// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/ownership/ownership_activate.h"

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_msg.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/ownership/owner_block.h"
#include "sw/device/silicon_creator/lib/ownership/ownership_key.h"

static rom_error_t activate(boot_svc_msg_t *msg, boot_data_t *bootdata) {
  size_t len = (uintptr_t)&msg->ownership_activate_req.signature -
               (uintptr_t)&msg->ownership_activate_req.primary_bl0_slot;
  // First check if page1 is even in a valid state for a transfer.
  if (owner_block_page1_valid_for_transfer(bootdata) != kHardenedBoolTrue) {
    return kErrorOwnershipInvalidInfoPage;
  }

  // Check the activation key and the nonce.
  if (ownership_key_validate(/*page=*/1, kOwnershipKeyActivate,
                             &msg->ownership_activate_req.signature,
                             &msg->ownership_activate_req.primary_bl0_slot,
                             len) == kHardenedBoolFalse) {
    return kErrorOwnershipInvalidSignature;
  }
  if (!nonce_equal(&msg->ownership_activate_req.nonce, &bootdata->nonce)) {
    return kErrorOwnershipInvalidNonce;
  }

  // Seal page one to this chip.
  owner_block_page_seal(/*page=*/1);

  // TODO(cfrantz): Consider reading back the flash pages to check that the
  // flash writes succeeded.
  //
  // Program the sealed page into slot 1.
  HARDENED_RETURN_IF_ERROR(flash_ctrl_info_erase(&kFlashCtrlInfoPageOwnerSlot1,
                                                 kFlashCtrlEraseTypePage));
  HARDENED_RETURN_IF_ERROR(flash_ctrl_info_write(
      &kFlashCtrlInfoPageOwnerSlot1, 0,
      sizeof(owner_page[1]) / sizeof(uint32_t), &owner_page[1]));

  // Program the same data into slot 0.
  HARDENED_RETURN_IF_ERROR(flash_ctrl_info_erase(&kFlashCtrlInfoPageOwnerSlot0,
                                                 kFlashCtrlEraseTypePage));
  HARDENED_RETURN_IF_ERROR(flash_ctrl_info_write(
      &kFlashCtrlInfoPageOwnerSlot0, 0,
      sizeof(owner_page[1]) / sizeof(uint32_t), &owner_page[1]));

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
    case kOwnershipStateLockedUpdate:
    case kOwnershipStateUnlockedAny:
    case kOwnershipStateUnlockedEndorsed:
      error = activate(msg, bootdata);
      break;
    default:
        /* nothing */;
  }
  boot_svc_ownership_activate_res_init(
      error == kErrorWriteBootdataThenReboot ? kErrorOk : error,
      &msg->ownership_activate_res);
  return error;
}
