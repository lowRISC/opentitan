// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/ownership/ownership_key.h"

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/drivers/kmac.h"
#include "sw/device/silicon_creator/lib/nonce.h"
#include "sw/device/silicon_creator/lib/ownership/owner_verify.h"

#include "hw/top/flash_ctrl_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// RAM copy of the owner INFO pages from flash.
extern owner_block_t owner_page[2];

OT_WEAK const owner_keydata_t *const kNoOwnerRecoveryKey;

static bool is_signature_empty(const owner_signature_t *signature) {
  for (size_t i = 0; i < ARRAYSIZE(signature->raw); ++i) {
    if (signature->raw[i] != 0)
      return false;
  }
  return true;
}

const owner_detached_signature_t *ownership_signature_scan(
    uintptr_t start, size_t length, uint32_t command, const nonce_t *nonce) {
  if (length < sizeof(owner_detached_signature_t))
    return NULL;
  length -= sizeof(owner_detached_signature_t);
  uintptr_t end = start + length;
  while (start < end) {
    const owner_detached_signature_t *sig =
        (const owner_detached_signature_t *)start;
    if (sig->header.tag == kTlvTagDetachedSignature &&
        sig->header.length == sizeof(owner_detached_signature_t) &&
        sig->header.version.major == 0 && sig->command == command &&
        nonce_equal(&sig->nonce, nonce)) {
      return sig;
    }
    start += FLASH_CTRL_PARAM_BYTES_PER_PAGE;
  }
  return NULL;
}

rom_error_t ownership_key_validate(size_t page, ownership_key_t key,
                                   uint32_t command, const nonce_t *nonce,
                                   const owner_signature_t *signature,
                                   const void *message, size_t len,
                                   uint32_t *flash_exec) {
  const ecdsa_p256_signature_t *ecdsa = NULL;
  const sigverify_spx_signature_t *spx = NULL;
  uint32_t key_alg = owner_page[page].ownership_key_alg;
  if (!is_signature_empty(signature)) {
    if (key_alg != kOwnershipKeyAlgEcdsaP256) {
      return kErrorOwnershipInvalidAlgorithm;
    }
    ecdsa = &signature->ecdsa;
  } else {
    const owner_detached_signature_t *detached = ownership_signature_scan(
        TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR,
        TOP_EARLGREY_FLASH_CTRL_MEM_SIZE_BYTES, command, nonce);
    if (detached == NULL) {
      return kErrorOwnershipSignatureNotFound;
    }
    uint32_t category =
        owner_page[page].ownership_key_alg & kOwnershipKeyAlgCategoryMask;
    switch (category) {
      case kOwnershipKeyAlgCategoryEcdsa:
        ecdsa = &detached->signature.ecdsa;
        break;
      case kOwnershipKeyAlgCategorySpx:
        spx = &detached->signature.spx;
        break;
      case kOwnershipKeyAlgCategoryHybrid:
        ecdsa = &detached->signature.hybrid.ecdsa;
        spx = &detached->signature.hybrid.spx;
        break;
      default:
        return kErrorOwnershipInvalidAlgorithm;
    }
  }
  hmac_digest_t digest;
  hmac_sha256(message, len, &digest);

  if ((key & kOwnershipKeyUnlock) == kOwnershipKeyUnlock) {
    if (owner_verify(key_alg, &owner_page[page].unlock_key, ecdsa, spx, NULL, 0,
                     NULL, 0, message, len, &digest, flash_exec) == kErrorOk) {
      return kErrorOk;
    }
  }
  if ((key & kOwnershipKeyActivate) == kOwnershipKeyActivate) {
    if (owner_verify(key_alg, &owner_page[page].activate_key, ecdsa, spx, NULL,
                     0, NULL, 0, message, len, &digest,
                     flash_exec) == kErrorOk) {
      return kErrorOk;
    }
  }
  if (kNoOwnerRecoveryKey &&
      (key & kOwnershipKeyRecovery) == kOwnershipKeyRecovery) {
    if (owner_verify(key_alg, kNoOwnerRecoveryKey, ecdsa, spx, NULL, 0, NULL, 0,
                     message, len, &digest, flash_exec) == kErrorOk) {
      return kErrorOk;
    }
  }
  if (owner_verify(key_alg, &owner_page[page].owner_key, ecdsa, spx, NULL, 0,
                   NULL, 0, message, len, &digest, flash_exec) == kErrorOk) {
    return kErrorOk;
  }
  return kErrorOwnershipInvalidSignature;
}

rom_error_t ownership_seal_init(void) {
  const sc_keymgr_diversification_t diversifier = {
      .salt = {4004, 8008, 8080, 1802, 6800, 6502, 6809, 8088},
      .version = 0,
  };
  HARDENED_RETURN_IF_ERROR(sc_keymgr_generate_key(
      kScKeymgrDestKmac, kScKeymgrKeyTypeSealing, diversifier));
  HARDENED_RETURN_IF_ERROR(kmac_kmac256_hw_configure());
  kmac_kmac256_set_prefix("Ownership", 9);
  return kErrorOk;
}

rom_error_t ownership_seal_clear(void) {
  return sc_keymgr_sideload_clear(kScKeymgrDestKmac);
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
      .read = (uint8_t)read,
      .write = (uint8_t)write,
      .erase = (uint8_t)write,
  };
  flash_ctrl_info_perms_set(&kFlashCtrlInfoPageOwnerSecret, perm);
}

rom_error_t ownership_secret_new(uint32_t prior_key_alg,
                                 const owner_keydata_t *prior_owner_key) {
  owner_secret_page_t secret;

  secret_page_enable(/*read=*/kMultiBitBool4True, /*write=*/kMultiBitBool4True);
  rom_error_t error =
      flash_ctrl_info_read(&kFlashCtrlInfoPageOwnerSecret, 0,
                           sizeof(secret) / sizeof(uint32_t), &secret);
  if (error != kErrorOk) {
    if (kDeviceType == kDeviceSilicon) {
      // This should never happen on silicon because this page is initialized
      // during personalization.
      goto exitproc;
    } else {
      // This should only happen on the FPGA during the first ownership
      // transfer.
      HARDENED_CHECK_NE(error, kErrorOk);
      HARDENED_CHECK_NE(kDeviceType, kDeviceSilicon);
      error = flash_ctrl_info_erase(&kFlashCtrlInfoPageOwnerSecret,
                                    kFlashCtrlEraseTypePage);
      memset(&secret, 0xFF, sizeof(secret));
    }
  }
  if (error != kErrorOk)
    goto exitproc;

  // Compute the ownership hash chain:
  // owner_history = HASH(owner_history || new_owner_key)
  hmac_sha256_init();
  hmac_sha256_update(&secret.owner_history, sizeof(secret.owner_history));
  size_t keysz = sizeof(*prior_owner_key);
  switch (prior_key_alg & kOwnershipKeyAlgCategoryMask) {
    case kOwnershipKeyAlgCategoryEcdsa:
      keysz = sizeof(prior_owner_key->ecdsa);
      break;
    case kOwnershipKeyAlgCategorySpx:
      keysz = sizeof(prior_owner_key->spx);
      break;
    case kOwnershipKeyAlgCategoryHybrid:
      keysz = sizeof(prior_owner_key->hybrid);
      break;
    default:;
  }
  hmac_sha256_update(prior_owner_key, keysz);
  hmac_sha256_process();
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
  hmac_sha256_update(prior_owner_key, keysz);
  hmac_sha256_process();
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
  if (error != kErrorOk) {
    // If there was an error reading the history, use all ones as a result.
    memset(history, 0xFF, sizeof(*history));
  }
  secret_page_enable(/*read=*/kMultiBitBool4False,
                     /*write=*/kMultiBitBool4False);
  return error;
}
