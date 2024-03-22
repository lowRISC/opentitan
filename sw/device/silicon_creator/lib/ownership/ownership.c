// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/ownership/ownership.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/ownership/ecdsa.h"
#include "sw/device/silicon_creator/lib/ownership/owner_keys.h"
#include "sw/device/silicon_creator/lib/ownership/ownership.h"

// RAM copy of the owner INFO pages from flash.
owner_block_t owner_page[2];

rom_error_t ownership_init(void) {
  flash_ctrl_perms_t perm = {
      .read = kMultiBitBool4True,
      .write = kMultiBitBool4True,
      .erase = kMultiBitBool4True,
  };
  flash_ctrl_info_perms_set(&kFlashCtrlInfoPageOwnerSlot0, perm);
  flash_ctrl_info_perms_set(&kFlashCtrlInfoPageOwnerSlot1, perm);
  HARDENED_RETURN_IF_ERROR(flash_ctrl_info_read(
      &kFlashCtrlInfoPageOwnerSlot0, 0,
      sizeof(owner_page[0]) / sizeof(uint32_t), &owner_page[0]));
  HARDENED_RETURN_IF_ERROR(flash_ctrl_info_read(
      &kFlashCtrlInfoPageOwnerSlot1, 0,
      sizeof(owner_page[1]) / sizeof(uint32_t), &owner_page[1]));

  // TODO(cfrantz): validate owner pages.
  // For now, just validate the signature on the page
  size_t len = (uintptr_t)&owner_page[0].signature - (uintptr_t)&owner_page[0];
  hardened_bool_t result;
  result =
      ownership_key_validate(/*page=*/0, kOwnershipKeyOwner,
                             &owner_page[0].signature, &owner_page[0], len);
  if (result == kHardenedBoolFalse) {
    // If the page is bad, destroy the RAM copy.
    memset(&owner_page[0], 0xFF, sizeof(owner_page[0]));
  }
  result =
      ownership_key_validate(/*page=*/0, kOwnershipKeyOwner,
                             &owner_page[0].signature, &owner_page[0], len);
  if (result == kHardenedBoolFalse) {
    // If the page is bad, destroy the RAM copy;.
    memset(&owner_page[1], 0xFF, sizeof(owner_page[1]));
  }

  // TOOD(cfrantz):
  // Depending on ownership state:
  // - kOwnershipStateLockedOwner:
  //     - Make sure page0 and page1 are identical and fix if not.
  //     - Set up flash config.
  //     - Enumerate application keys.
  // - kOwnershipStateLockedUpdate:
  //     - Allow the pages to be different if the owner keys are the same.
  //     - Set up flash config: primary from page0, secondary from page 1.
  //     - Enumerate application keys from both pages.
  // - kOwnershipStateUnlockedAny: Allow the pages to be different.
  //     - Allow the pages to be different.
  //     - Set up flash config: primary from page0, secondary from page 1.
  //     - Enumerate application keys from both pages.
  // - kOwnershipStateUnlockedEndorsed: Allow the pages to be different.
  //     - Allow the pages to be different.
  //     - Set up flash config: primary from page0, secondary from page 1.
  //     - Enumerate application keys from both pages.
  // - kOwnershipStateLockedNone: Allow the pages to be different.
  //     - Disaster state. Do nothing and wait for remediation via
  //       the recovery key.

  return kErrorOk;
}

hardened_bool_t ownership_key_validate(size_t page, ownership_key_t key,
                                       const owner_signature_t *signature,
                                       const void *message, size_t len) {
  if ((key & kOwnershipKeyUnlock) == kOwnershipKeyUnlock) {
    if (ecdsa_verify_message(&owner_page[page].unlock_key, signature, message,
                             len) == kHardenedBoolTrue) {
      return kHardenedBoolTrue;
    }
  }
  if ((key & kOwnershipKeyActivate) == kOwnershipKeyActivate) {
    if (ecdsa_verify_message(&owner_page[page].activate_key, signature, message,
                             len) == kHardenedBoolTrue) {
      return kHardenedBoolTrue;
    }
  }
  if (kOwnershipNoOwnerRecoveryKey &&
      (key & kOwnershipKeyRecovery) == kOwnershipKeyRecovery) {
    if (ecdsa_verify_message(kOwnershipNoOwnerRecoveryKey, signature, message,
                             len) == kHardenedBoolTrue) {
      return kHardenedBoolTrue;
    }
  }
  return ecdsa_verify_message(&owner_page[page].owner_key, signature, message,
                              len);
}
