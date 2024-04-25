// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include "sw/device/silicon_creator/lib/ownership/ownership.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/dbg_print.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/ownership/ecdsa.h"
#include "sw/device/silicon_creator/lib/ownership/owner_block.h"
#include "sw/device/silicon_creator/lib/ownership/ownership.h"
#include "sw/device/silicon_creator/lib/ownership/ownership_key.h"

// RAM copy of the owner INFO pages from flash.
owner_block_t owner_page[2];
owner_page_status_t owner_page_valid[2];

static owner_page_status_t owner_page_validity_check(size_t page) {
  size_t seal_len = (uintptr_t)&owner_page[0].seal - (uintptr_t)&owner_page[0];
  size_t sig_len =
      (uintptr_t)&owner_page[0].signature - (uintptr_t)&owner_page[0];

  // TODO(cfrantz): validate owner pages.
  // For now, we consider the seal to be just the sha256 over the page.
  // This really needs to be the KMAC over the page with a keymgr-created
  // sealing secret.
  hmac_digest_t digest;
  hmac_sha256(&owner_page[page], seal_len, &digest);
  if (hardened_memeq(owner_page[page].seal, digest.digest,
                     ARRAYSIZE(digest.digest)) == kHardenedBoolTrue) {
    return kOwnerPageStatusSealed;
  }
  hardened_bool_t result = ownership_key_validate(page, kOwnershipKeyOwner,
                                                  &owner_page[page].signature,
                                                  &owner_page[page], sig_len);
  if (result == kHardenedBoolFalse) {
    // If the page is bad, destroy the RAM copy.
    memset(&owner_page[page], 0x5a, sizeof(owner_page[0]));
    return kOwnerPageStatusInvalid;
  }
  return kOwnerPageStatusSigned;
}

OT_WEAK rom_error_t test_owner_init(boot_data_t *bootdata,
                                    owner_config_t *config,
                                    owner_application_keyring_t *keyring) {
  dbg_printf("error: no owner.\r\n");
  return kErrorOwnershipNoOwner;
}

static rom_error_t locked_owner_init(boot_data_t *bootdata,
                                     owner_config_t *config,
                                     owner_application_keyring_t *keyring) {
  if (owner_page_valid[0] == kOwnerPageStatusInvalid &&
      owner_page_valid[1] == kOwnerPageStatusSealed) {
    // Page 0 bad, Page 1 good: copy page 1 to page 0.
    memcpy(&owner_page[0], &owner_page[1], sizeof(owner_page[0]));
    HARDENED_RETURN_IF_ERROR(flash_ctrl_info_erase(
        &kFlashCtrlInfoPageOwnerSlot0, kFlashCtrlEraseTypePage));
    HARDENED_RETURN_IF_ERROR(flash_ctrl_info_write(
        &kFlashCtrlInfoPageOwnerSlot0, 0,
        sizeof(owner_page[0]) / sizeof(uint32_t), &owner_page[0]));
    owner_page_valid[0] = owner_page_valid[1];
  } else if (owner_page_valid[1] == kOwnerPageStatusInvalid &&
             owner_page_valid[0] == kOwnerPageStatusSealed) {
    // Page 1 bad, Page 0 good: copy page 0 to page 1.
    memcpy(&owner_page[1], &owner_page[0], sizeof(owner_page[0]));
    HARDENED_RETURN_IF_ERROR(flash_ctrl_info_erase(
        &kFlashCtrlInfoPageOwnerSlot1, kFlashCtrlEraseTypePage));
    HARDENED_RETURN_IF_ERROR(flash_ctrl_info_write(
        &kFlashCtrlInfoPageOwnerSlot1, 0,
        sizeof(owner_page[1]) / sizeof(uint32_t), &owner_page[1]));
    owner_page_valid[1] = owner_page_valid[0];
  } else if (owner_page_valid[0] != kOwnerPageStatusSealed &&
             owner_page_valid[1] != kOwnerPageStatusSealed) {
    // Neither page is valid; go to the Recovery state.
    dbg_printf("error: both owner pages invalid.\r\n");
    bootdata->ownership_state = kOwnershipStateRecovery;
    nonce_new(&bootdata->nonce);
    HARDENED_RETURN_IF_ERROR(boot_data_write(bootdata));
    return kErrorOwnershipBadInfoPage;
  }
  HARDENED_RETURN_IF_ERROR(owner_block_parse(&owner_page[0], config, keyring));
  HARDENED_RETURN_IF_ERROR(owner_block_flash_apply(config->flash, kBootSlotA,
                                                   bootdata->primary_bl0_slot));
  HARDENED_RETURN_IF_ERROR(owner_block_flash_apply(config->flash, kBootSlotB,
                                                   bootdata->primary_bl0_slot));
  HARDENED_RETURN_IF_ERROR(owner_block_info_apply(config->info));
  // TODO: apply rescue config
  return kErrorOk;
}

hardened_bool_t ownership_page1_valid_for_transfer(boot_data_t *bootdata) {
  if (bootdata->ownership_state == kOwnershipStateLockedOwner &&
      owner_page_valid[1] == kOwnerPageStatusSealed) {
    return kHardenedBoolTrue;
  }
  if (owner_page_valid[1] == kOwnerPageStatusSigned) {
    hmac_digest_t digest;
    switch (bootdata->ownership_state) {
      case kOwnershipStateUnlockedAny:
        // In UnlockedAny, any valid (signed) Owner Page 1 is acceptable.
        return kHardenedBoolTrue;
      case kOwnershipStateLockedUpdate:
        // In LockedUpdate, the owner key must be the same.  If not,
        // skip parsing of Owner Page 1.
        if (hardened_memeq(
                owner_page[0].owner_key.key, owner_page[1].owner_key.key,
                ARRAYSIZE(owner_page[0].owner_key.key)) == kHardenedBoolTrue) {
          return kHardenedBoolTrue;
        }
        break;
      case kOwnershipStateUnlockedEndorsed:
        // In UnlockedEndorsed, the owner key must match the key endorsed by the
        // next_owner field in bootdata.  If not, skip parsing owner page 1.
        hmac_sha256(owner_page[1].owner_key.key,
                    sizeof(owner_page[1].owner_key.key), &digest);
        if (hardened_memeq(bootdata->next_owner, digest.digest,
                           ARRAYSIZE(digest.digest)) == kHardenedBoolTrue) {
          return kHardenedBoolTrue;
        }
        break;
      default:
          /* nothing */;
    }
  }
  return kHardenedBoolFalse;
}

static rom_error_t unlocked_init(boot_data_t *bootdata, owner_config_t *config,
                                 owner_application_keyring_t *keyring) {
  uint32_t secondary =
      bootdata->primary_bl0_slot == kBootSlotA ? kBootSlotB : kBootSlotA;
  if (bootdata->ownership_state == kOwnershipStateLockedUpdate &&
      owner_page_valid[0] != kOwnerPageStatusSealed) {
    // Owner Page 0 must be sealed in the "LockedUpdate" state.  If not,
    // go to the Recovery state.
    bootdata->ownership_state = kOwnershipStateRecovery;
    nonce_new(&bootdata->nonce);
    HARDENED_RETURN_IF_ERROR(boot_data_write(bootdata));
    return kErrorOwnershipBadInfoPage;
  }

  if (owner_page_valid[0] == kOwnerPageStatusSealed) {
    // Configure the primary half of the flash as Owner Page 0 requests.
    HARDENED_RETURN_IF_ERROR(
        owner_block_parse(&owner_page[0], config, keyring));
    HARDENED_RETURN_IF_ERROR(owner_block_flash_apply(
        config->flash, bootdata->primary_bl0_slot, bootdata->primary_bl0_slot));
  }

  if (ownership_page1_valid_for_transfer(bootdata) == kHardenedBoolTrue) {
    // If we passed the validity test for Owner Page 1, parse the configuration
    // and add its keys to the keyring.
    HARDENED_RETURN_IF_ERROR(
        owner_block_parse(&owner_page[1], config, keyring));
  }
  HARDENED_RETURN_IF_ERROR(owner_block_flash_apply(config->flash, secondary,
                                                   bootdata->primary_bl0_slot));
  HARDENED_RETURN_IF_ERROR(owner_block_info_apply(config->info));
  // TODO: apply rescue config
  return kErrorOk;
}

rom_error_t ownership_init(boot_data_t *bootdata, owner_config_t *config,
                           owner_application_keyring_t *keyring) {
  flash_ctrl_perms_t perm = {
      .read = kMultiBitBool4True,
      .write = kMultiBitBool4True,
      .erase = kMultiBitBool4True,
  };
  flash_ctrl_cfg_t cfg = {
      .scrambling = kMultiBitBool4True,
      .ecc = kMultiBitBool4True,
  };
  flash_ctrl_info_perms_set(&kFlashCtrlInfoPageOwnerSlot0, perm);
  flash_ctrl_info_cfg_set(&kFlashCtrlInfoPageOwnerSlot0, cfg);
  flash_ctrl_info_perms_set(&kFlashCtrlInfoPageOwnerSlot1, perm);
  flash_ctrl_info_cfg_set(&kFlashCtrlInfoPageOwnerSlot1, cfg);
  // We don't want to abort ownership setup if we fail to
  // read the INFO pages, so we discard the error result.
  if (flash_ctrl_info_read(&kFlashCtrlInfoPageOwnerSlot0, 0,
                           sizeof(owner_page[0]) / sizeof(uint32_t),
                           &owner_page[0]) == kErrorOk) {
    owner_page_valid[0] = owner_page_validity_check(0);
  } else {
    owner_page_valid[0] = kOwnerPageStatusInvalid;
    memset(&owner_page[0], 0xff, sizeof(owner_page[0]));
  }
  if (flash_ctrl_info_read(&kFlashCtrlInfoPageOwnerSlot1, 0,
                           sizeof(owner_page[1]) / sizeof(uint32_t),
                           &owner_page[1]) == kErrorOk) {
    owner_page_valid[1] = owner_page_validity_check(1);
  } else {
    owner_page_valid[1] = kOwnerPageStatusInvalid;
    memset(&owner_page[1], 0xff, sizeof(owner_page[1]));
  }

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
  // - kOwnershipStateRecovery: Allow the pages to be different.
  //     - Disaster state. Do nothing and wait for remediation via
  //       the recovery key.

  dbg_printf("ownership: %C\r\n", bootdata->ownership_state);
  owner_config_default(config);
  rom_error_t error = kErrorOwnershipNoOwner;
  switch (bootdata->ownership_state) {
    case kOwnershipStateLockedOwner:
      error = locked_owner_init(bootdata, config, keyring);
      break;
    case kOwnershipStateLockedUpdate:
      OT_FALLTHROUGH_INTENDED;
    case kOwnershipStateUnlockedAny:
      OT_FALLTHROUGH_INTENDED;
    case kOwnershipStateUnlockedEndorsed:
      error = unlocked_init(bootdata, config, keyring);
      break;
    default:
      // The `test_owner_init` function is weak and the default implementation
      // does nothing.
      error = test_owner_init(bootdata, config, keyring);
  }
  return error;
}

void ownership_page_seal(size_t page) {
  size_t seal_len = (uintptr_t)&owner_page[0].seal - (uintptr_t)&owner_page[0];
  hmac_digest_t digest;
  hmac_sha256(&owner_page[page], seal_len, &digest);
  memcpy(&owner_page[page].seal, digest.digest, sizeof(digest.digest));
}
