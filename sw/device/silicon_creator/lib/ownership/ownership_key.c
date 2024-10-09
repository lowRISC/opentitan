// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/ownership/ownership_key.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/drivers/kmac.h"
#include "sw/device/silicon_creator/lib/ownership/ecdsa.h"

// RAM copy of the owner INFO pages from flash.
extern owner_block_t owner_page[2];

OT_WEAK const owner_key_t *const kNoOwnerRecoveryKey;

hardened_bool_t ownership_key_validate(size_t page, ownership_key_t key,
                                       const owner_signature_t *signature,
                                       const void *message, size_t len) {
  if ((key & kOwnershipKeyUnlock) == kOwnershipKeyUnlock) {
    if (ecdsa_verify_message(&owner_page[page].unlock_key.ecdsa,
                             &signature->ecdsa, message,
                             len) == kHardenedBoolTrue) {
      return kHardenedBoolTrue;
    }
  }
  if ((key & kOwnershipKeyActivate) == kOwnershipKeyActivate) {
    if (ecdsa_verify_message(&owner_page[page].activate_key.ecdsa,
                             &signature->ecdsa, message,
                             len) == kHardenedBoolTrue) {
      return kHardenedBoolTrue;
    }
  }
  if (kNoOwnerRecoveryKey &&
      (key & kOwnershipKeyRecovery) == kOwnershipKeyRecovery) {
    if (ecdsa_verify_message(&kNoOwnerRecoveryKey->ecdsa, &signature->ecdsa,
                             message, len) == kHardenedBoolTrue) {
      return kHardenedBoolTrue;
    }
  }
  return ecdsa_verify_message(&owner_page[page].owner_key.ecdsa,
                              &signature->ecdsa, message, len);
}

rom_error_t ownership_seal_init(void) {
  const keymgr_diversification_t diversifier = {
      .salt = {4004, 8008, 8080, 1802, 6800, 6502, 6809, 8088},
      .version = 0,
  };
  HARDENED_RETURN_IF_ERROR(
      keymgr_generate_key(kKeymgrDestKmac, kKeymgrKeyTypeSealing, diversifier));
  HARDENED_RETURN_IF_ERROR(kmac_kmac256_hw_configure());
  kmac_kmac256_set_prefix("Ownership", 9);
  return kErrorOk;
}

static rom_error_t seal_generate(const owner_block_t *page, uint32_t *seal) {
  size_t sealed_len = offsetof(owner_block_t, seal);
  HARDENED_RETURN_IF_ERROR(kmac_kmac256_start());
  kmac_kmac256_absorb(page, sealed_len);
  return kmac_kmac256_final(seal, ARRAYSIZE(page->seal));
}

rom_error_t ownership_seal_page(size_t page) {
  owner_block_t *data = &owner_page[page];
  return seal_generate(data, data->seal);
}

rom_error_t ownership_seal_check(size_t page) {
  owner_block_t *data = &owner_page[page];
  uint32_t check[ARRAYSIZE(data->seal)];
  HARDENED_RETURN_IF_ERROR(seal_generate(data, check));
  hardened_bool_t result =
      hardened_memeq(data->seal, check, ARRAYSIZE(data->seal));
  if (result == kHardenedBoolTrue) {
    // Translate to kErrorOk.  A cast is sufficient because kHardenedBoolTrue
    // and kErrorOk have the same bit pattern.
    return (rom_error_t)result;
  }
  return kErrorOwnershipInvalidInfoPage;
}

static void reverse(void *buf, size_t len) {
  char *x = (char *)buf;
  char *y = x + len - 1;
  for (; x < y; ++x, --y) {
    char t = *x;
    *x = *y;
    *y = t;
  }
}

static void secret_page_enable(multi_bit_bool_t read, multi_bit_bool_t write) {
  flash_ctrl_perms_t perm = {
      .read = read,
      .write = write,
      .erase = write,
  };
  flash_ctrl_info_perms_set(&kFlashCtrlInfoPageOwnerSecret, perm);
}

rom_error_t ownership_secret_new(void) {
  owner_secret_page_t secret;

  secret_page_enable(/*read=*/kMultiBitBool4True, /*write=*/kMultiBitBool4True);
  rom_error_t error =
      flash_ctrl_info_read(&kFlashCtrlInfoPageOwnerSecret, 0,
                           sizeof(secret) / sizeof(uint32_t), &secret);
  if (error != kErrorOk) {
    HARDENED_CHECK_NE(error, kErrorOk);
    // This should only happen on the FPGA during the first ownership transfer.
    // TODO: What should we do if we ever encounter this error on silicon?
    // A successful erase and reprogram will "heal" the chip, but any
    // ownership history will be lost.
    error = flash_ctrl_info_erase(&kFlashCtrlInfoPageOwnerSecret,
                                  kFlashCtrlEraseTypePage);
    memset(&secret, 0xFF, sizeof(secret));
  }
  if (error != kErrorOk)
    goto exitproc;

  // Compute the ownership hash chain:
  // owner_history = HASH(owner_history || new_owner_key)
  hmac_sha256_init();
  hmac_sha256_update(&secret.owner_history, sizeof(secret.owner_history));
  size_t keysz = sizeof(owner_page[0].owner_key);
  switch (owner_page[0].ownership_key_alg) {
    case kOwnershipKeyAlgEcdsaP256:
      keysz = sizeof(owner_page[0].owner_key.ecdsa);
      break;
    default:;
  }
  hmac_sha256_update(&owner_page[0].owner_key, keysz);
  hmac_sha256_final(&secret.owner_history);
  // TODO(cfrantz): when merging to master, use the big-endian form of
  // the sha256 function to avoid the reversal operation at the end.
  reverse(&secret.owner_history, sizeof(secret.owner_history));

  // Generate a new owner secret seed.  This will completely disconnect
  // the keymgr state from the previous owner's keymgr state.
  // We hash the previous owner entropy with the new owner key.
  // owner_secret = HASH(owner_secret || new_owner_key)
  // TODO: is this sufficient, or should we generate new entropy?
  hmac_sha256_init();
  hmac_sha256_update(&secret.owner_secret, sizeof(secret.owner_secret));
  hmac_sha256_update(&owner_page[0].owner_key, keysz);
  hmac_sha256_final(&secret.owner_secret);

  error = flash_ctrl_info_erase(&kFlashCtrlInfoPageOwnerSecret,
                                kFlashCtrlEraseTypePage);
  if (error != kErrorOk)
    goto exitproc;
  error = flash_ctrl_info_write(&kFlashCtrlInfoPageOwnerSecret, 0,
                                sizeof(secret) / sizeof(uint32_t), &secret);

exitproc:
  secret_page_enable(/*read=*/kMultiBitBool4False,
                     /*write=*/kMultiBitBool4False);
  return error;
}

rom_error_t ownership_history_get(hmac_digest_t *history) {
  secret_page_enable(/*read=*/kMultiBitBool4True,
                     /*write=*/kMultiBitBool4False);
  rom_error_t error =
      flash_ctrl_info_read(&kFlashCtrlInfoPageOwnerSecret,
                           offsetof(owner_secret_page_t, owner_history),
                           sizeof(*history) / sizeof(uint32_t), history);
  secret_page_enable(/*read=*/kMultiBitBool4False,
                     /*write=*/kMultiBitBool4False);
  return error;
}
