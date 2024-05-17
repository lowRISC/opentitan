// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/ownership/ownership_key.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
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
