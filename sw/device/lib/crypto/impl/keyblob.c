// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/keyblob.h"

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/random_order.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/drivers/rv_core_ibex.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/status.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('k', 'b', 'b')

/**
 * Determine the number of bytes in one share of a blinded key.
 *
 * Normally, this is the same length as the unblinded key material. However, in
 * the case of some asymmetric keys, the shares might be longer.
 *
 * @param config Key configuration.
 * @return Number of bytes in one share of the blinded key.
 */
static size_t keyblob_share_num_bytes(const otcrypto_key_config_t config) {
  // Get the key type from the top 16 bits of the full mode.
  otcrypto_key_type_t key_type = (otcrypto_key_type_t)(config.key_mode >> 16);
  switch (launder32(key_type)) {
    case kOtcryptoKeyTypeEcc:
      // ECC keys have 64 extra redundant bits per share.
      HARDENED_CHECK_EQ(config.key_mode >> 16, kOtcryptoKeyTypeEcc);
      return config.key_length + (64 / 8);
    case kOtcryptoKeyTypeRsa:
      // RSA key shares are the same size as the unmasked key.
      // TODO: update once masking is implemented for RSA keys.
      HARDENED_CHECK_EQ(config.key_mode >> 16, kOtcryptoKeyTypeRsa);
      return config.key_length;
    default:
      // Symmetric key shares are simply the same size as the unmasked key.
      HARDENED_CHECK_NE(config.key_mode >> 16, kOtcryptoKeyTypeEcc);
      HARDENED_CHECK_NE(config.key_mode >> 16, kOtcryptoKeyTypeRsa);
      return config.key_length;
  }
  HARDENED_TRAP();
}

size_t keyblob_share_num_words(const otcrypto_key_config_t config) {
  size_t len_bytes = keyblob_share_num_bytes(config);
  return ceil_div(len_bytes, sizeof(uint32_t));
}

size_t keyblob_num_words(const otcrypto_key_config_t config) {
  if (launder32(config.hw_backed) == kHardenedBoolTrue) {
    HARDENED_CHECK_EQ(config.hw_backed, kHardenedBoolTrue);
    return kKeyblobHwBackedWords;
  }
  HARDENED_CHECK_NE(config.hw_backed, kHardenedBoolTrue);
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
static status_t check_keyblob_length(const otcrypto_blinded_key_t *key) {
  size_t num_words = keyblob_num_words(key->config);
  if (launder32(key->keyblob_length) == num_words * sizeof(uint32_t)) {
    HARDENED_CHECK_EQ(key->keyblob_length, num_words * sizeof(uint32_t));
    HARDENED_CHECK_LE(key->keyblob_length / sizeof(uint32_t), num_words);
    return OTCRYPTO_OK;
  }
  return OTCRYPTO_BAD_ARGS;
}

status_t keyblob_to_shares(const otcrypto_blinded_key_t *key, uint32_t **share0,
                           uint32_t **share1) {
  // Double-check the length of the keyblob.
  HARDENED_TRY(check_keyblob_length(key));

  size_t key_words = keyblob_share_num_words(key->config);
  *share0 = key->keyblob;
  *share1 = &key->keyblob[key_words];
  return OTCRYPTO_OK;
}

status_t keyblob_from_shares(const uint32_t *share0, const uint32_t *share1,
                             const otcrypto_key_config_t config,
                             uint32_t *keyblob) {
  // Entropy complex must be initialized for `hardened_memcpy`.
  HARDENED_TRY(entropy_complex_check());

  // Randomize the keyblob contents before writing shares.
  hardened_memshred(keyblob, keyblob_num_words(config));

  size_t share_words = keyblob_share_num_words(config);
  hardened_memcpy(keyblob, share0, share_words);
  hardened_memcpy(keyblob + share_words, share1, share_words);
  return OTCRYPTO_OK;
}

status_t keyblob_buffer_to_keymgr_diversification(
    const uint32_t *keyblob, otcrypto_key_mode_t mode,
    keymgr_diversification_t *diversification) {
  // Set the version to the first word of the keyblob.
  diversification->version = launder32(keyblob[0]);

  // Entropy complex must be initialized for `hardened_memcpy`.
  HARDENED_TRY(entropy_complex_check());

  // Copy the remainder of the keyblob into the salt.
  hardened_memcpy(diversification->salt, &keyblob[1], kKeymgrSaltNumWords - 1);

  // Set the key mode as the last word of the salt.
  diversification->salt[kKeymgrSaltNumWords - 1] = launder32(mode);

  HARDENED_CHECK_EQ(diversification->version, keyblob[0]);
  HARDENED_CHECK_EQ(hardened_memeq(diversification->salt, &keyblob[1],
                                   kKeymgrSaltNumWords - 1),
                    kHardenedBoolTrue);
  HARDENED_CHECK_EQ(diversification->salt[kKeymgrSaltNumWords - 1], mode);
  return OTCRYPTO_OK;
}

status_t keyblob_to_keymgr_diversification(
    const otcrypto_blinded_key_t *key,
    keymgr_diversification_t *diversification) {
  if (launder32(key->config.hw_backed) != kHardenedBoolTrue ||
      key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(key->config.hw_backed, kHardenedBoolTrue);

  if (key->keyblob_length != kKeyblobHwBackedBytes) {
    return OTCRYPTO_BAD_ARGS;
  }

  return keyblob_buffer_to_keymgr_diversification(
      key->keyblob, key->config.key_mode, diversification);
}

status_t keyblob_ensure_xor_masked(const otcrypto_key_config_t config) {
  // Reject hardware-backed keys, since the keyblob is not the actual key
  // material in this case but the version/salt.
  if (launder32(config.hw_backed) != kHardenedBoolFalse) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(config.hw_backed, kHardenedBoolFalse);

  // Get the key type from the top 16 bits of the full mode.
  otcrypto_key_type_t key_type =
      (otcrypto_key_type_t)(launder32((uint32_t)config.key_mode) >> 16);
  int32_t result = (int32_t)launder32((uint32_t)(OTCRYPTO_OK.value ^ key_type));
  switch (launder32(key_type)) {
    case kOtcryptoKeyTypeAes:
      HARDENED_CHECK_EQ(config.key_mode >> 16, kOtcryptoKeyTypeAes);
      result ^= launder32(kOtcryptoKeyTypeAes);
      break;
    case kOtcryptoKeyTypeHmac:
      HARDENED_CHECK_EQ(config.key_mode >> 16, kOtcryptoKeyTypeHmac);
      result ^= launder32(kOtcryptoKeyTypeHmac);
      break;
    case kOtcryptoKeyTypeKmac:
      HARDENED_CHECK_EQ(config.key_mode >> 16, kOtcryptoKeyTypeKmac);
      result ^= launder32(kOtcryptoKeyTypeKmac);
      break;
    case kOtcryptoKeyTypeKdf:
      HARDENED_CHECK_EQ(config.key_mode >> 16, kOtcryptoKeyTypeKdf);
      result ^= launder32(kOtcryptoKeyTypeKdf);
      break;
    case kOtcryptoKeyTypeEcc:
      // Asymmetric!
      return OTCRYPTO_BAD_ARGS;
    case kOtcryptoKeyTypeRsa:
      // Asymmetric!
      return OTCRYPTO_BAD_ARGS;
    default:
      // Unrecognized key type.
      return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_NE(config.key_mode >> 16, kOtcryptoKeyTypeEcc);
  HARDENED_CHECK_NE(config.key_mode >> 16, kOtcryptoKeyTypeRsa);

  // If we get here, the result should be OTCRYPTO_OK.
  return (status_t){.value = result};
}

status_t keyblob_from_key_and_mask(const uint32_t *key, const uint32_t *mask,
                                   const otcrypto_key_config_t config,
                                   uint32_t *keyblob) {
  // Check that the key is masked with XOR.
  HARDENED_TRY(keyblob_ensure_xor_masked(config));

  // share0 = key ^ mask, share1 = mask
  size_t key_words = keyblob_share_num_words(config);
  uint32_t share0[key_words];
  size_t i = 0;
  for (; launder32(i) < key_words; i++) {
    share0[i] = key[i] ^ mask[i];
  }
  HARDENED_CHECK_EQ(i, key_words);

  return keyblob_from_shares(share0, mask, config, keyblob);
}

/**
 * Combines two word buffers with XOR.
 *
 * Callers should ensure the entropy complex is up before calling this
 * function.  The implementation uses random-order hardening primitives for
 * side-channel defense.
 *
 * @param[in,out] x Pointer to the first operand (modified in-place).
 * @param y Pointer to the second operand.
 * @param word_len Length in words of each operand.
 */
void hardened_xor(uint32_t *restrict x, const uint32_t *restrict y,
                  size_t word_len) {
  // Generate a random ordering.
  random_order_t order;
  random_order_init(&order, word_len);
  size_t count = 0;
  size_t expected_count = random_order_len(&order);

  // Create some random values for decoy operations.
  uint32_t decoys[8];
  hardened_memshred(decoys, ARRAYSIZE(decoys));

  // Cast pointers to `uintptr_t` to erase their provenance.
  uintptr_t x_addr = (uintptr_t)x;
  uintptr_t y_addr = (uintptr_t)y;
  uintptr_t decoy_addr = (uintptr_t)&decoys;

  // XOR the mask with the first share. This loop is modelled off the one in
  // `hardened_memcpy`; see the comments there for more details.
  size_t byte_len = word_len * sizeof(uint32_t);
  for (; launderw(count) < expected_count; count = launderw(count) + 1) {
    size_t byte_idx = launderw(random_order_advance(&order)) * sizeof(uint32_t);

    // Prevent the compiler from re-ordering the loop.
    barrierw(byte_idx);

    // Calculate pointers. The x and y pointers might not be valid, but in this
    // case they will not be selected.
    uintptr_t xp = x_addr + byte_idx;
    uintptr_t yp = y_addr + byte_idx;
    uintptr_t decoy1 = decoy_addr + (byte_idx % sizeof(decoys));
    uintptr_t decoy2 =
        decoy_addr +
        ((byte_idx + (sizeof(decoys) / 2) + sizeof(uint32_t)) % sizeof(decoys));

    // Select in constant-time either the real pointers or decoys.
    void *xv = (void *)launderw(
        ct_cmovw(ct_sltuw(launderw(byte_idx), byte_len), xp, decoy1));
    void *yv = (void *)launderw(
        ct_cmovw(ct_sltuw(launderw(byte_idx), byte_len), yp, decoy2));

    // Perform an XOR in either the decoy array or the real array.
    write_32(read_32(xv) ^ read_32(yv), xv);
  }
  RANDOM_ORDER_HARDENED_CHECK_DONE(order);
  HARDENED_CHECK_EQ(count, expected_count);
}

status_t keyblob_remask(otcrypto_blinded_key_t *key) {
  // Check that the key is masked with XOR.
  HARDENED_TRY(keyblob_ensure_xor_masked(key->config));

  // Check that the entropy complex is up and properly configured.
  HARDENED_TRY(entropy_complex_check());

  uint32_t *share0;
  uint32_t *share1;
  HARDENED_TRY(keyblob_to_shares(key, &share0, &share1));

  // Generate a fresh mask the size of one share.
  size_t key_share_words = keyblob_share_num_words(key->config);
  uint32_t mask[key_share_words];
  hardened_memshred(mask, key_share_words);

  // XOR each share with the mask.
  hardened_xor(share0, mask, key_share_words);
  hardened_xor(share1, mask, key_share_words);

  // Update the key checksum.
  key->checksum = integrity_blinded_checksum(key);
  return OTCRYPTO_OK;
}

status_t keyblob_key_unmask(const otcrypto_blinded_key_t *key,
                            size_t unmasked_key_len, uint32_t *unmasked_key) {
  if (key == NULL || unmasked_key == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (keyblob_share_num_words(key->config) != unmasked_key_len) {
    return OTCRYPTO_BAD_ARGS;
  }

  uint32_t *share0;
  uint32_t *share1;
  HARDENED_TRY(keyblob_to_shares(key, &share0, &share1));

  for (size_t i = 0; i < unmasked_key_len; i++) {
    unmasked_key[i] = share0[i] ^ share1[i];
  }
  return OTCRYPTO_OK;
}

status_t keyblob_sideload_key_otbn(const otcrypto_blinded_key_t *key) {
  keymgr_diversification_t diversification;
  HARDENED_TRY(keyblob_to_keymgr_diversification(key, &diversification));
  return keymgr_generate_key_otbn(diversification);
}
