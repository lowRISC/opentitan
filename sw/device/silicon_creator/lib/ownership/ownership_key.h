// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_OWNERSHIP_KEY_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_OWNERSHIP_KEY_H_

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/ownership/datatypes.h"

/**
 * The OwnershipNoOwnerRecoveryKey is a silicon_creator key that allows
 * recovery of a device should it get into the Recovery state (ie:
 * a state where there is no valid owner).
 */
extern const owner_keydata_t *const kNoOwnerRecoveryKey;

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

typedef struct owner_secret_page {
  /** Owner entropy. */
  hmac_digest_t owner_secret;
  /** Hash chain of previous owners. */
  hmac_digest_t owner_history;
} owner_secret_page_t;

/**
 * Validate that a message was signed with a given owner key.
 * If the message fails verification with the Activate or Unlock key,
 * the verification is retried with the Owner key.
 *
 * @param page Owner-page on which the key resides.
 * @param key Which key (or keys) to use to validate the message.
 * @param command The bootsvc command or entity this validate is for.
 * @param nonce The current ROM_EXT nonce.
 * @param signature The signature over the message.
 * @param message Pointer to the message.
 * @param len Size of the message.
 * @param flash_exec The magic value signifying whether the signature was
 * verified.
 * @return kErrorOk if the message is valid.
 */
rom_error_t ownership_key_validate(size_t page, ownership_key_t key,
                                   uint32_t command, const nonce_t *nonce,
                                   const owner_signature_t *signature,
                                   const void *message, size_t len,
                                   uint32_t *flash_exec);

/**
 * Initialize sealing.
 *
 * Initializes the KMAC block to create a KMAC-256 seal based on a key
 * created by keymgr.
 *
 * @return Success or error code.
 */
rom_error_t ownership_seal_init(void);

/**
 * Clear the sideloaded key in the KMAC block.
 *
 * @return Success or error code.
 */
rom_error_t ownership_seal_clear(void);

/**
 * Generate a seal for an ownership page.
 *
 * @param page Owner page for which to generate the sealing value.
 * @return Success or error code.
 */
rom_error_t ownership_seal_page(size_t page);

/**
 * Check the seal on an ownership page.
 *
 * @param page Owner page on which to check the seal.
 * @return Success or error code.
 */
rom_error_t ownership_seal_check(size_t page);

/**
 * Replace the owner secret with new entropy and update the ownership history.
 *
 * @param prior_key_alg The key algorithm of the prior owner_key.
 * @param prior_owner_key The prior owner key.
 * @return Success or error code.
 */
rom_error_t ownership_secret_new(uint32_t prior_key_alg,
                                 const owner_keydata_t *prior_owner_key);

/**
 * Retrieve the owner history digest from the OwnerSecret page.
 *
 * @param history Digest of all previous owner keys.
 * @return Success or error code.
 */
rom_error_t ownership_history_get(hmac_digest_t *history);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_OWNERSHIP_KEY_H_
