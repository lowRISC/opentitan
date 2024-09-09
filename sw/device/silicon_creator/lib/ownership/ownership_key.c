// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/ownership/ownership_key.h"

#include "sw/device/lib/base/hardened.h"
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
