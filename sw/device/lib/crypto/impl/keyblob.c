// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/keyblob.h"

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/status.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('k', 'b', 'b')

size_t keyblob_share_num_words(const crypto_key_config_t config) {
  size_t len_bytes = config.key_length;
  if (len_bytes % sizeof(uint32_t) == 0) {
    return len_bytes / sizeof(uint32_t);
  }
  return (len_bytes / sizeof(uint32_t)) + 1;
}

size_t keyblob_num_words(const crypto_key_config_t config) {
  return 2 * keyblob_share_num_words(config);
}

/**
 * Check that the keyblob length matches expectations from the key config.
 *
 * Returns an OK status if the keyblob length is correct, a BAD_ARGS status
 * otherwise.
 *
 * @param key Blinded key.
 * @returns OK if the keyblob length is correct, BAD_ARGS otherwise.
 */
static status_t check_keyblob_length(const crypto_blinded_key_t *key) {
  size_t num_words = keyblob_num_words(key->config);
  if (key->keyblob_length == num_words * sizeof(uint32_t)) {
    HARDENED_CHECK_EQ(key->keyblob_length, num_words * sizeof(uint32_t));
    HARDENED_CHECK_LE(key->keyblob_length / sizeof(uint32_t), num_words);
    return OTCRYPTO_OK;
  }
  return OTCRYPTO_BAD_ARGS;
}

status_t keyblob_to_shares(const crypto_blinded_key_t *key, uint32_t **share0,
                           uint32_t **share1) {
  // Double-check the length of the keyblob.
  HARDENED_TRY(check_keyblob_length(key));

  size_t key_words = keyblob_share_num_words(key->config);
  *share0 = key->keyblob;
  *share1 = &key->keyblob[key_words];
  return OTCRYPTO_OK;
}

void keyblob_from_shares(const uint32_t *share0, const uint32_t *share1,
                         const crypto_key_config_t config, uint32_t *keyblob) {
  size_t share_words = keyblob_share_num_words(config);
  hardened_memcpy(keyblob, share0, share_words);
  hardened_memcpy(keyblob + share_words, share1, share_words);
}

void keyblob_from_key_and_mask(const uint32_t *key, const uint32_t *mask,
                               const crypto_key_config_t config,
                               uint32_t *keyblob) {
  size_t key_words = keyblob_share_num_words(config);
  // share0 = key ^ mask, share1 = mask
  uint32_t share0[key_words];
  for (size_t i = 0; i < key_words; i++) {
    share0[i] = key[i] ^ mask[i];
  }
  keyblob_from_shares(share0, mask, config, keyblob);
}

status_t keyblob_remask(crypto_blinded_key_t *key, const uint32_t *mask) {
  size_t key_share_words = keyblob_share_num_words(key->config);
  size_t keyblob_words = keyblob_num_words(key->config);

  // Construct a new keyblob by re-masking.
  size_t i = 0;
  for (; launder32(i) < keyblob_words; i++) {
    key->keyblob[i] ^= mask[i % key_share_words];
  }
  HARDENED_CHECK_EQ(i, keyblob_words);

  // Update the key checksum.
  key->checksum = integrity_blinded_checksum(key);
  return OTCRYPTO_OK;
}
