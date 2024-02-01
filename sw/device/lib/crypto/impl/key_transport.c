// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/key_transport.h"

#include "sw/device/lib/base/hardened_memory.h"
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
  keyblob_from_shares(key_share0.data, key_share1.data, blinded_key->config,
                      blinded_key->keyblob);
  blinded_key->checksum = integrity_blinded_checksum(blinded_key);
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_export_blinded_key(
    const otcrypto_blinded_key_t blinded_key, otcrypto_word32_buf_t key_share0,
    otcrypto_word32_buf_t key_share1) {
  if (blinded_key.keyblob == NULL || key_share0.data == NULL ||
      key_share1.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check key integrity.
  if (launder32(integrity_blinded_key_check(&blinded_key)) !=
      kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(integrity_blinded_key_check(&blinded_key),
                    kHardenedBoolTrue);

  // Ensure the key is symmetric and not hardware-backed.
  HARDENED_TRY(keyblob_ensure_xor_masked(blinded_key.config));

  // Check that key is exportable.
  if (launder32(blinded_key.config.exportable) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(blinded_key.config.exportable, kHardenedBoolTrue);

  // Check the lengths of the shares.
  size_t share_words = launder32(keyblob_share_num_words(blinded_key.config));
  if (launder32(key_share0.len) != share_words ||
      launder32(key_share1.len) != share_words) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(key_share0.len,
                    keyblob_share_num_words(blinded_key.config));
  HARDENED_CHECK_EQ(key_share1.len,
                    keyblob_share_num_words(blinded_key.config));

  // Check the length of the keyblob.
  size_t keyblob_words = launder32(keyblob_num_words(blinded_key.config));
  if ((blinded_key.keyblob_length % sizeof(uint32_t) != 0) ||
      (blinded_key.keyblob_length / sizeof(uint32_t) != keyblob_words)) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(blinded_key.keyblob_length,
                    keyblob_words * sizeof(uint32_t));

  // Get pointers to the internal shares and copy them into output buffers.
  uint32_t *keyblob_share0;
  uint32_t *keyblob_share1;
  HARDENED_TRY(
      keyblob_to_shares(&blinded_key, &keyblob_share0, &keyblob_share1));
  hardened_memcpy(key_share0.data, keyblob_share0, key_share0.len);
  hardened_memcpy(key_share1.data, keyblob_share1, key_share1.len);
  return OTCRYPTO_OK;
}
