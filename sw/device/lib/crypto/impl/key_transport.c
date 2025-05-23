// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/key_transport.h"

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/impl/aes_kwp/aes_kwp.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/drbg.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('k', 't', 'r')

otcrypto_status_t otcrypto_symmetric_keygen(
    otcrypto_const_byte_buf_t perso_string, otcrypto_blinded_key_t *key) {
  if (key == NULL || key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Ensure that the key material is masked with XOR; this will fail on
  // hardware-backed or non-symmetric keys.
  HARDENED_TRY(keyblob_ensure_xor_masked(key->config));

  // Ensure that the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  // Get pointers to the shares within the keyblob. Fails if the key length
  // doesn't match the mode.
  uint32_t *share0;
  uint32_t *share1;
  HARDENED_TRY(keyblob_to_shares(key, &share0, &share1));

  // Construct buffers to direct the DRBG output into the keyblob.
  otcrypto_word32_buf_t share0_buf = {
      .data = share0,
      .len = keyblob_share_num_words(key->config),
  };
  otcrypto_word32_buf_t share1_buf = {
      .data = share1,
      .len = keyblob_share_num_words(key->config),
  };

  // Randomize the memory before writing the shares.
  hardened_memshred(share0_buf.data, share0_buf.len);
  hardened_memshred(share1_buf.data, share1_buf.len);

  // Construct an empty buffer for the "additional input" to the DRBG generate
  // function.
  otcrypto_const_byte_buf_t empty = {.data = NULL, .len = 0};

  // Generate each share of the key independently.
  HARDENED_TRY(otcrypto_drbg_instantiate(perso_string));
  HARDENED_TRY(otcrypto_drbg_generate(empty, share0_buf));
  HARDENED_TRY(otcrypto_drbg_generate(empty, share1_buf));

  // Populate the checksum and return.
  key->checksum = integrity_blinded_checksum(key);
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_hw_backed_key(uint32_t version,
                                         const uint32_t salt[7],
                                         otcrypto_blinded_key_t *key) {
  if (key == NULL || key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (key->keyblob_length != 8 * sizeof(uint32_t) ||
      key->config.hw_backed != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Get the key type from the top 16 bits of the full mode and ensure that it
  // is not RSA. All other key types are acceptable for hardware-backed keys.
  otcrypto_key_type_t key_type =
      (otcrypto_key_type_t)(key->config.key_mode >> 16);
  if (key_type == kOtcryptoKeyTypeRsa) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Copy the version and salt into the keyblob.
  key->keyblob[0] = version;
  memcpy(&key->keyblob[1], salt, 7 * sizeof(uint32_t));

  // Set the checksum.
  key->checksum = integrity_blinded_checksum(key);

  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_wrapped_key_len(const otcrypto_key_config_t config,
                                           size_t *wrapped_num_words) {
  // Check that the total wrapped key length will fit in 32 bits.
  size_t config_num_words = sizeof(otcrypto_key_config_t) / sizeof(uint32_t);
  if (keyblob_num_words(config) > UINT32_MAX - config_num_words - 2) {
    return OTCRYPTO_BAD_ARGS;
  }

  // A wrapped key includes:
  //   - The full key configuration
  //   - The key checksum (32 bits)
  //   - The keyblob length (in words) as a 32-bit word
  //   - The keyblob
  *wrapped_num_words = config_num_words + 2 + keyblob_num_words(config);

  // We need to add 64 bits for the AES-KWP prefix.
  *wrapped_num_words += 2;

  // The number of words needs to be rounded up to the next multiple of 64 bits.
  if (*wrapped_num_words % 2 == 1) {
    *wrapped_num_words += 1;
  }

  return OTCRYPTO_OK;
}

/**
 * Extract an AES-KWP key encryption key from the blinded key struct.
 *
 * Also checks the key's integrity and mode.
 *
 * @param key_kek Blinded key encryption key.
 * @param[out] aes_key Destination AES key struct.
 * @return Result of the operation.
 */
static status_t aes_kwp_key_construct(const otcrypto_blinded_key_t *key_kek,
                                      aes_key_t *aes_key) {
  // Key integrity check.
  if (launder32(integrity_blinded_key_check(key_kek)) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(integrity_blinded_key_check(key_kek), kHardenedBoolTrue);

  // Check the key mode.
  if (launder32((uint32_t)key_kek->config.key_mode) != kOtcryptoKeyModeAesKwp) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(key_kek->config.key_mode, kOtcryptoKeyModeAesKwp);

  // Set the mode of the underlying AES key to ECB (since this is the
  // underlying block cipher mode for KWP).
  aes_key->mode = kAesCipherModeEcb;

  if (key_kek->config.hw_backed == kHardenedBoolTrue) {
    // Call keymgr to sideload the key into AES.
    keymgr_diversification_t diversification;
    HARDENED_TRY(keyblob_to_keymgr_diversification(key_kek, &diversification));
    HARDENED_TRY(keymgr_generate_key_aes(diversification));
  } else if (key_kek->config.hw_backed != kHardenedBoolFalse) {
    return OTCRYPTO_BAD_ARGS;
  }
  aes_key->sideload = key_kek->config.hw_backed;

  // Set the AES key length (in words).
  aes_key->key_len = keyblob_share_num_words(key_kek->config);

  // Get pointers to the individual shares.
  uint32_t *share0;
  uint32_t *share1;
  HARDENED_TRY(keyblob_to_shares(key_kek, &share0, &share1));
  aes_key->key_shares[0] = share0;
  aes_key->key_shares[1] = share1;

  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_key_wrap(const otcrypto_blinded_key_t *key_to_wrap,
                                    const otcrypto_blinded_key_t *key_kek,
                                    otcrypto_word32_buf_t wrapped_key) {
  if (key_to_wrap == NULL || key_to_wrap->keyblob == NULL || key_kek == NULL ||
      key_kek->keyblob == NULL || wrapped_key.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Ensure the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  // Check the integrity of the key material we are wrapping.
  if (launder32(integrity_blinded_key_check(key_to_wrap)) !=
      kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(integrity_blinded_key_check(key_to_wrap),
                    kHardenedBoolTrue);

  // Check the length of the output buffer.
  size_t exp_len;
  HARDENED_TRY(otcrypto_wrapped_key_len(key_to_wrap->config, &exp_len));
  if (wrapped_key.len != exp_len) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the integrity/lengths/mode of the key encryption key, and construct
  // an internal AES key.
  aes_key_t kek;
  HARDENED_TRY(aes_kwp_key_construct(key_kek, &kek));

  // Check the keyblob length.
  uint32_t keyblob_words = keyblob_num_words(key_to_wrap->config);
  if (key_to_wrap->keyblob_length != keyblob_words * sizeof(uint32_t)) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check that the configuration is aligned.
  if (misalignment32_of((uintptr_t)&key_to_wrap->config) != 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Create the plaintext by copying the key configuration, checksum, keyblob
  // length, and keyblob into a buffer.
  uint32_t config_words = sizeof(otcrypto_key_config_t) / sizeof(uint32_t);
  size_t plaintext_num_words = config_words + 2 + keyblob_words;
  uint32_t plaintext[plaintext_num_words];
  hardened_memshred(plaintext, ARRAYSIZE(plaintext));
  hardened_memcpy(plaintext, (uint32_t *)&key_to_wrap->config, config_words);
  plaintext[config_words] = key_to_wrap->checksum;
  plaintext[config_words + 1] = keyblob_words;
  hardened_memcpy(plaintext + config_words + 2, key_to_wrap->keyblob,
                  keyblob_words);

  // Wrap the key.
  return aes_kwp_wrap(kek, plaintext, sizeof(plaintext), wrapped_key.data);
}

otcrypto_status_t otcrypto_key_unwrap(otcrypto_const_word32_buf_t wrapped_key,
                                      const otcrypto_blinded_key_t *key_kek,
                                      hardened_bool_t *success,
                                      otcrypto_blinded_key_t *unwrapped_key) {
  *success = kHardenedBoolFalse;

  if (wrapped_key.data == NULL || key_kek == NULL || key_kek->keyblob == NULL ||
      success == NULL || unwrapped_key == NULL ||
      unwrapped_key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Ensure the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  // Check the integrity/lengths/mode of the key encryption key, and construct
  // an internal AES key.
  aes_key_t kek;
  HARDENED_TRY(aes_kwp_key_construct(key_kek, &kek));

  // Check that the configuration is aligned.
  if (misalignment32_of((uintptr_t)&unwrapped_key->config) != 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Unwrap the key.
  uint32_t plaintext[wrapped_key.len];
  hardened_memshred(plaintext, ARRAYSIZE(plaintext));
  HARDENED_TRY(aes_kwp_unwrap(kek, wrapped_key.data,
                              wrapped_key.len * sizeof(uint32_t), success,
                              plaintext));

  if (launder32(*success) != kHardenedBoolTrue) {
    *success = kHardenedBoolFalse;
    return OTCRYPTO_OK;
  }
  HARDENED_CHECK_EQ(*success, kHardenedBoolTrue);

  // Set back to false while we check other conditions.
  *success = kHardenedBoolFalse;

  // Extract the key configuration.
  uint32_t config_words = sizeof(otcrypto_key_config_t) / sizeof(uint32_t);
  hardened_memcpy((uint32_t *)&unwrapped_key->config, plaintext, config_words);

  // Extract the checksum and keyblob length.
  unwrapped_key->checksum = plaintext[config_words];
  uint32_t keyblob_words = plaintext[config_words + 1];
  if (keyblob_words != keyblob_num_words(unwrapped_key->config)) {
    *success = kHardenedBoolFalse;
    return OTCRYPTO_OK;
  }

  // Extract the keyblob.
  if (unwrapped_key->keyblob_length != keyblob_words * sizeof(uint32_t)) {
    return OTCRYPTO_BAD_ARGS;
  }
  hardened_memcpy(unwrapped_key->keyblob, plaintext + config_words + 2,
                  keyblob_words);

  // Finally, check the integrity of the key material we unwrapped.
  *success = integrity_blinded_key_check(unwrapped_key);
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_import_blinded_key(
    const otcrypto_const_word32_buf_t key_share0,
    const otcrypto_const_word32_buf_t key_share1,
    otcrypto_blinded_key_t *blinded_key) {
  if (blinded_key == NULL || blinded_key->keyblob == NULL ||
      key_share0.data == NULL || key_share1.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Ensure the key is symmetric and not hardware-backed.
  HARDENED_TRY(keyblob_ensure_xor_masked(blinded_key->config));

  // Check the lengths of the shares.
  size_t share_words = launder32(keyblob_share_num_words(blinded_key->config));
  if (launder32(key_share0.len) != share_words ||
      launder32(key_share1.len) != share_words) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(key_share0.len,
                    keyblob_share_num_words(blinded_key->config));
  HARDENED_CHECK_EQ(key_share1.len,
                    keyblob_share_num_words(blinded_key->config));

  // Check the length of the keyblob.
  size_t keyblob_words = launder32(keyblob_num_words(blinded_key->config));
  if ((blinded_key->keyblob_length % sizeof(uint32_t) != 0) ||
      (blinded_key->keyblob_length / sizeof(uint32_t) != keyblob_words)) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(blinded_key->keyblob_length,
                    keyblob_words * sizeof(uint32_t));

  // Construct the blinded key.
  HARDENED_TRY(keyblob_from_shares(key_share0.data, key_share1.data,
                                   blinded_key->config, blinded_key->keyblob));
  blinded_key->checksum = integrity_blinded_checksum(blinded_key);
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_export_blinded_key(
    const otcrypto_blinded_key_t *blinded_key, otcrypto_word32_buf_t key_share0,
    otcrypto_word32_buf_t key_share1) {
  if (blinded_key->keyblob == NULL || key_share0.data == NULL ||
      key_share1.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Ensure the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  // Check key integrity.
  if (launder32(integrity_blinded_key_check(blinded_key)) !=
      kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(integrity_blinded_key_check(blinded_key),
                    kHardenedBoolTrue);

  // Ensure the key is symmetric and not hardware-backed.
  HARDENED_TRY(keyblob_ensure_xor_masked(blinded_key->config));

  // Check that key is exportable.
  if (launder32(blinded_key->config.exportable) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(blinded_key->config.exportable, kHardenedBoolTrue);

  // Check the lengths of the shares.
  size_t share_words = launder32(keyblob_share_num_words(blinded_key->config));
  if (launder32(key_share0.len) != share_words ||
      launder32(key_share1.len) != share_words) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(key_share0.len,
                    keyblob_share_num_words(blinded_key->config));
  HARDENED_CHECK_EQ(key_share1.len,
                    keyblob_share_num_words(blinded_key->config));

  // Randomize the destination buffers.
  hardened_memshred(key_share0.data, key_share0.len);
  hardened_memshred(key_share1.data, key_share1.len);

  // Check the length of the keyblob.
  size_t keyblob_words = launder32(keyblob_num_words(blinded_key->config));
  if ((blinded_key->keyblob_length % sizeof(uint32_t) != 0) ||
      (blinded_key->keyblob_length / sizeof(uint32_t) != keyblob_words)) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(blinded_key->keyblob_length,
                    keyblob_words * sizeof(uint32_t));

  // Get pointers to the internal shares and copy them into output buffers.
  uint32_t *keyblob_share0;
  uint32_t *keyblob_share1;
  HARDENED_TRY(
      keyblob_to_shares(blinded_key, &keyblob_share0, &keyblob_share1));
  hardened_memcpy(key_share0.data, keyblob_share0, key_share0.len);
  hardened_memcpy(key_share1.data, keyblob_share1, key_share1.len);
  return OTCRYPTO_OK;
}
