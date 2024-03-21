// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_OWNERSHIP_KEY_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_OWNERSHIP_KEY_H_

#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/ownership/datatypes.h"

/**
 * The OwnershipNoOwnerRecoveryKey is a silicon_creator key that allows
 * recovery of a device should it get into the Recovery state (ie:
 * a state where there is no valid owner).
 */
extern const owner_key_t *const kNoOwnerRecoveryKey;

typedef enum ownership_key {
  /** The owner_key in the owner page. */
  kOwnershipKeyOwner = 0x1111,

  /** The activate_key in the owner page. */
  kOwnershipKeyActivate = 0x2222,

  /** The unlock_key in the owner page. */
  kOwnershipKeyUnlock = 0x4444,

  /** The silicon_creator no_owner_recovery key. */
  kOwnershipKeyRecovery = 0x8888,
} ownership_key_t;

/**
 * Validate that a message was signed with a given owner key.
 * If the message fails verification with the Activate or Unlock key,
 * the verification is retried with the Owner key.
 *
 * @param page Owner-page on which the key resides.
 * @param key Which key (or keys) to use to validate the message.
 * @param signature The signature over the message.
 * @param message Pointer to the message.
 * @param len Size of the message.
 * @return kHardenedBoolTrue if the message is valid.
 */
hardened_bool_t ownership_key_validate(size_t page, ownership_key_t key,
                                       const owner_signature_t *signature,
                                       const void *message, size_t len);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_OWNERSHIP_KEY_H_
