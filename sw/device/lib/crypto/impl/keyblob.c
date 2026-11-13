// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/keyblob.h"

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/random_order.h"
#include "sw/device/lib/crypto/drivers/rv_core_ibex.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/integrity.h"

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
  if (launder32(config.key_length) == 0) {
    return 0;
  }

  // Get the key type from the top 16 bits of the full mode.
  otcrypto_key_type_t key_type = (otcrypto_key_type_t)(config.key_mode >> 16);
  switch (launder32(key_type)) {
    case kOtcryptoKeyTypeEcc:
      // ECC keys have 64 extra redundant bits per share.
      HARDENED_CHECK_EQ(config.key_mode >> 16, kOtcryptoKeyTypeEcc);
      if (launder32(config.key_length) > UINT32_MAX - (64 / 8)) {
        return 0;
      }
      return config.key_length + (64 / 8);
    case kOtcryptoKeyTypeRsa:
      // RSA key shares are the same size as the unmasked key.
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
  otcrypto_key_type_t key_type = (otcrypto_key_type_t)(config.key_mode >> 16);
  if (launder32(config.hw_backed) == kHardenedBoolTrue &&
      launder32(key_type) != kOtcryptoKeyTypeEcc &&
      launder32(len_bytes) != kKeymgrOutputShareNumWords * sizeof(uint32_t)) {
    return 0;
  }
  if (launder32(key_type) == kOtcryptoKeyTypeHmac ||
      launder32(key_type) == kOtcryptoKeyTypeTdes) {
    return ceil_div(len_bytes, sizeof(uint32_t));
  }
  if (launder32(len_bytes % sizeof(uint32_t)) != 0) {
    return 0;
  }
  return len_bytes / sizeof(uint32_t);
}

size_t keyblob_num_words(const otcrypto_key_config_t config) {
  if (launder32(config.hw_backed) == kHardenedBoolTrue) {
    HARDENED_CHECK_EQ(config.hw_backed, kHardenedBoolTrue);
    return kKeyblobHwBackedWords;
  }
  HARDENED_CHECK_NE(config.hw_backed, kHardenedBoolTrue);

  // Get the key type from the top 16 bits of the full mode.
  otcrypto_key_type_t key_type = (otcrypto_key_type_t)(config.key_mode >> 16);
  if (launder32(key_type) == kOtcryptoKeyTypeRsa) {
    // RSA private keyblobs store d (in 1 or 2 shares), n, and a 32-bit
    // checksum.
    HARDENED_CHECK_EQ(config.key_mode >> 16, kOtcryptoKeyTypeRsa);
#ifdef OTCRYPTO_DISABLE_KEYBLOB_MASKING
    return 2 * keyblob_share_num_words(config) + 1;
#else
    return 3 * keyblob_share_num_words(config) + 1;
#endif
  }
  HARDENED_CHECK_NE(config.key_mode >> 16, kOtcryptoKeyTypeRsa);
#ifdef OTCRYPTO_DISABLE_KEYBLOB_MASKING
  return keyblob_share_num_words(config);
#else
  return 2 * keyblob_share_num_words(config);
#endif
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
  if (launder32(key->config.key_length) >
          kOtcryptoWrappedKeyMaxWords * sizeof(uint32_t) ||
      launder32(keyblob_share_num_words(key->config)) == 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  size_t num_words = keyblob_num_words(key->config);
  if (launder32(key->keyblob_length) == num_words * sizeof(uint32_t)) {
    HARDENED_CHECK_EQ(key->keyblob_length, num_words * sizeof(uint32_t));
    HARDENED_CHECK_LE(key->keyblob_length / sizeof(uint32_t), num_words);
    return OTCRYPTO_OK;
  }
  return OTCRYPTO_BAD_ARGS;
}

#ifdef OTCRYPTO_DISABLE_KEYBLOB_MASKING
static uint32_t s_share0[kOtcryptoWrappedKeyMaxWords];
static uint32_t s_share1[kOtcryptoWrappedKeyMaxWords];

static const uint32_t kP256Order[10] = {
    0xfc632551, 0xf3b9cac2, 0xa7179e84, 0xbce6faad, 0xffffffff,
    0xffffffff, 0x00000000, 0xffffffff, 0x00000000, 0x00000000};
static const uint32_t kP384Order[14] = {
    0xccc52973, 0xecec196a, 0x48b0a77a, 0x581a0db2, 0xf4372ddf,
    0xc7634d81, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
    0xffffffff, 0xffffffff, 0x00000000, 0x00000000};

static const uint32_t *ecc_order_get(otcrypto_key_mode_t key_mode) {
  switch (key_mode) {
    case kOtcryptoKeyModeEcdsaP256:
    case kOtcryptoKeyModeEcdhP256:
      return kP256Order;
    case kOtcryptoKeyModeEcdsaP384:
    case kOtcryptoKeyModeEcdhP384:
      return kP384Order;
    default:
      return NULL;
  }
}
#endif

status_t keyblob_to_shares(const otcrypto_blinded_key_t *key, uint32_t **share0,
                           uint32_t **share1) {
  if (key->config.hw_backed != kHardenedBoolFalse) {
    return OTCRYPTO_BAD_ARGS;
  }
  // Double-check the length of the keyblob.
  HARDENED_TRY(check_keyblob_length(key));

  size_t key_words = keyblob_share_num_words(key->config);
#ifdef OTCRYPTO_DISABLE_KEYBLOB_MASKING
  const uint32_t *order = ecc_order_get(key->config.key_mode);
  if (order != NULL) {
    uint32_t d_red[14];
    HARDENED_TRY(hardened_mod_reduce(key->keyblob, order, key_words, d_red));
    HARDENED_TRY(hardened_memshred(s_share0, key_words));
    HARDENED_TRY(hardened_mod_reduce(s_share0, order, key_words, s_share1));
    HARDENED_TRY(hardened_sub_mod(d_red, s_share1, order, key_words, s_share0));
  } else if (key->config.key_mode == kOtcryptoKeyModeEd25519 ||
             key->config.key_mode == kOtcryptoKeyModeX25519) {
    HARDENED_TRY(hardened_memshred(s_share1, key_words));
    memset(&s_share1[key_words - 2], 0, 2 * sizeof(uint32_t));
    HARDENED_TRY(hardened_sub(key->keyblob, s_share1, key_words - 2, s_share0));
    memset(&s_share0[key_words - 2], 0, 2 * sizeof(uint32_t));
  } else {
    HARDENED_TRY(hardened_memshred(s_share1, key_words));
    HARDENED_TRY(hardened_xor(key->keyblob, s_share1, key_words, s_share0));
  }
  *share0 = s_share0;
  *share1 = s_share1;
  return OTCRYPTO_OK;
#else
  *share0 = key->keyblob;
  *share1 = &key->keyblob[key_words];
  return OTCRYPTO_OK;
#endif
}

status_t keyblob_from_shares(const uint32_t *share0, const uint32_t *share1,
                             const otcrypto_key_config_t config,
                             uint32_t *keyblob) {
  size_t share_words = keyblob_share_num_words(config);
#ifdef OTCRYPTO_DISABLE_KEYBLOB_MASKING
  const uint32_t *order = ecc_order_get(config.key_mode);
  if (order != NULL) {
    HARDENED_TRY(hardened_mod_reduce(share0, order, share_words, s_share0));
    HARDENED_TRY(hardened_mod_reduce(share1, order, share_words, s_share1));
    return hardened_add_mod(s_share0, s_share1, order, share_words, keyblob);
  }
  if (share0 != keyblob) {
    // Randomize the keyblob contents before writing shares.
    HARDENED_TRY(hardened_memshred(keyblob, keyblob_num_words(config)));
    HARDENED_TRY(hardened_memcpy(keyblob, share0, share_words));
    HARDENED_CHECK_EQ(hardened_memeq(share0, keyblob, share_words),
                      kHardenedBoolTrue);
  }
  return hardened_xor_in_place(keyblob, share1, share_words);
#else
  // Randomize the keyblob contents before writing shares.
  HARDENED_TRY(hardened_memshred(keyblob, keyblob_num_words(config)));

  HARDENED_TRY(hardened_memcpy(keyblob, share0, share_words));
  HARDENED_TRY(hardened_memcpy(keyblob + share_words, share1, share_words));
  HARDENED_CHECK_EQ(hardened_memeq(share0, keyblob, share_words),
                    kHardenedBoolTrue);
  HARDENED_CHECK_EQ(hardened_memeq(share1, keyblob + share_words, share_words),
                    kHardenedBoolTrue);
  return OTCRYPTO_OK;
#endif
}

status_t keyblob_buffer_to_keymgr_diversification(
    const uint32_t *keyblob, otcrypto_key_mode_t mode,
    keymgr_diversification_t *diversification) {
  // Set the version to the first word of the keyblob.
  diversification->version = launder32(keyblob[0]);

  // Copy the remainder of the keyblob into the salt.
  HARDENED_TRY(hardened_memcpy(diversification->salt, &keyblob[1],
                               kKeymgrSaltNumWords - 1));

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
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif
  if (launder32(key->config.hw_backed) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(key->config.hw_backed, kHardenedBoolTrue);

  if (launder32(keyblob_share_num_words(key->config)) == 0 ||
      (key->keyblob_length != kKeyblobHwBackedBytes &&
       key->keyblob_length != kSwKeyblobHwBackedBytes)) {
    return OTCRYPTO_BAD_ARGS;
  }

  return keyblob_buffer_to_keymgr_diversification(
      key->keyblob, key->config.key_mode, diversification);
}

status_t keyblob_to_keymgr_attestation_diversification(
    const otcrypto_blinded_key_t *key,
    keymgr_diversification_t *diversification) {
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif
  if (launder32(key->config.hw_backed) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(key->config.hw_backed, kHardenedBoolTrue);

  if (launder32(keyblob_share_num_words(key->config)) == 0 ||
      (key->keyblob_length != kCdiKeyblobHwBackedBytes &&
       key->keyblob_length != kSwKeyblobHwBackedBytes)) {
    return OTCRYPTO_BAD_ARGS;
  }

  diversification->version = launder32(key->keyblob[0]);

  HARDENED_TRY(hardened_memcpy(diversification->salt, &key->keyblob[1],
                               kKeymgrSaltNumWords));

  HARDENED_CHECK_EQ(diversification->version, key->keyblob[0]);
  HARDENED_CHECK_EQ(hardened_memeq(diversification->salt, &key->keyblob[1],
                                   kKeymgrSaltNumWords),
                    kHardenedBoolTrue);

  return OTCRYPTO_OK;
}

status_t keyblob_ensure_xor_masked(const otcrypto_key_config_t config) {
  if (launder32(config.key_length) >
          kOtcryptoWrappedKeyMaxWords * sizeof(uint32_t) ||
      launder32(keyblob_share_num_words(config)) == 0) {
    return OTCRYPTO_BAD_ARGS;
  }

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
  otcrypto_key_type_t key_type_used = launder32(0);
  switch (launder32(key_type)) {
    case kOtcryptoKeyTypeAes:
      key_type_used = launder32(key_type_used) | kOtcryptoKeyTypeAes;
      result ^= launder32(kOtcryptoKeyTypeAes);
      break;
    case kOtcryptoKeyTypeTdes:
      key_type_used = launder32(key_type_used) | kOtcryptoKeyTypeTdes;
      result ^= launder32(kOtcryptoKeyTypeTdes);
      break;
    case kOtcryptoKeyTypeHmac:
      key_type_used = launder32(key_type_used) | kOtcryptoKeyTypeHmac;
      result ^= launder32(kOtcryptoKeyTypeHmac);
      break;
    case kOtcryptoKeyTypeKmac:
      key_type_used = launder32(key_type_used) | kOtcryptoKeyTypeKmac;
      result ^= launder32(kOtcryptoKeyTypeKmac);
      break;
    case kOtcryptoKeyTypeKdf:
      key_type_used = launder32(key_type_used) | kOtcryptoKeyTypeKdf;
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
  // Check if we landed in the correct case statement. Use ORs for this to
  // avoid that multiple cases were executed.
  HARDENED_CHECK_EQ(launder32(key_type_used), key_type);

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
#ifdef OTCRYPTO_DISABLE_KEYBLOB_MASKING
  (void)mask;
  return hardened_memcpy(keyblob, key, keyblob_share_num_words(config));
#else
  // share0 = key ^ mask, share1 = mask
  size_t key_words = keyblob_share_num_words(config);
  if (key_words > kOtcryptoWrappedKeyMaxWords) {
    // COVERAGE (FI CM) Redundant check; keyblob_ensure_xor_masked already
    // bounds the key length.
    return OTCRYPTO_BAD_ARGS;
  }
  uint32_t share0[kOtcryptoWrappedKeyMaxWords];
  HARDENED_TRY(hardened_xor(key, mask, key_words, share0));

  return keyblob_from_shares(share0, mask, config, keyblob);
#endif
}

status_t keyblob_remask(otcrypto_blinded_key_t *key) {
  // Check that the key is masked with XOR.
  HARDENED_TRY(keyblob_ensure_xor_masked(key->config));

#ifndef OTCRYPTO_DISABLE_KEYBLOB_MASKING
  uint32_t *share0;
  uint32_t *share1;
  HARDENED_TRY(keyblob_to_shares(key, &share0, &share1));

  // Generate a fresh mask the size of one share.
  size_t key_share_words = keyblob_share_num_words(key->config);
  if (key_share_words > kOtcryptoWrappedKeyMaxWords) {
    // COVERAGE (FI CM) Redundant check; keyblob_ensure_xor_masked already
    // bounds the key length.
    return OTCRYPTO_BAD_ARGS;
  }
  uint32_t mask[kOtcryptoWrappedKeyMaxWords];
  HARDENED_TRY(hardened_memshred(mask, key_share_words));

  // XOR each share with the mask.
  HARDENED_TRY(hardened_xor_in_place(share0, mask, key_share_words));
  HARDENED_TRY(hardened_xor_in_place(share1, mask, key_share_words));
#endif

  // Update the key checksum.
  key->checksum = otcrypto_integrity_blinded_checksum(key);
  return OTCRYPTO_OK;
}

status_t keyblob_key_unmask(const otcrypto_blinded_key_t *key,
                            size_t unmasked_key_len, uint32_t *unmasked_key) {
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (key == NULL || unmasked_key == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif
  if (keyblob_share_num_words(key->config) != unmasked_key_len) {
    return OTCRYPTO_BAD_ARGS;
  }

  uint32_t *share0;
  uint32_t *share1;
  HARDENED_TRY(keyblob_to_shares(key, &share0, &share1));

  HARDENED_TRY(hardened_xor(share0, share1, unmasked_key_len, unmasked_key));

  return OTCRYPTO_OK;
}

status_t keyblob_sideload_key_otbn(const otcrypto_blinded_key_t *key) {
  keymgr_diversification_t diversification;
  HARDENED_TRY(keyblob_to_keymgr_diversification(key, &diversification));
  return keymgr_generate_key_otbn(diversification, kHardenedBoolFalse);
}
