// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/kdf.h"

#include "sw/device/lib/base/math.h"
#include "sw/device/lib/crypto/drivers/kmac.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/mac.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('k', 'd', 'f')

/**
 * Check if the string contains a 0x00 byte.
 *
 * @param buffer Inspected string.
 * @return OK or error.
 */
static status_t check_zero_byte(const otcrypto_const_byte_buf_t buffer) {
  for (size_t i = 0; i < buffer.len; i++) {
    if (buffer.data[i] == 0x00) {
      return OTCRYPTO_BAD_ARGS;
    }
  }
  return OTCRYPTO_OK;
}

/**
 * Infer the digest length in 32-bit words for the given hash function.
 *
 * @param key_mode HMAC key mode.
 * @param[out] digest_words Number of words in the hash digest.
 * @return OK or error.
 */
static status_t digest_num_words_from_key_mode(otcrypto_key_mode_t key_mode,
                                               size_t *digest_words) {
  *digest_words = 0;
  switch (launder32(key_mode)) {
    case kOtcryptoKeyModeHmacSha256:
      HARDENED_CHECK_EQ(key_mode, kOtcryptoKeyModeHmacSha256);
      *digest_words = 256 / 32;
      break;
    case kOtcryptoKeyModeHmacSha384:
      HARDENED_CHECK_EQ(key_mode, kOtcryptoKeyModeHmacSha384);
      *digest_words = 384 / 32;
      break;
    case kOtcryptoKeyModeHmacSha512:
      HARDENED_CHECK_EQ(key_mode, kOtcryptoKeyModeHmacSha512);
      *digest_words = 512 / 32;
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_NE(*digest_words, 0);
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_kdf_hmac_ctr(
    const otcrypto_blinded_key_t key_derivation_key,
    const otcrypto_const_byte_buf_t kdf_label,
    const otcrypto_const_byte_buf_t kdf_context, size_t required_byte_len,
    otcrypto_blinded_key_t *keying_material) {
  // Check NULL pointers.
  if (keying_material == NULL || keying_material->keyblob == NULL ||
      key_derivation_key.keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (launder32(keying_material->config.security_level) !=
          kOtcryptoKeySecurityLevelLow ||
      launder32(key_derivation_key.config.security_level) !=
          kOtcryptoKeySecurityLevelLow) {
    // The underlying HMAC implementation is not currently hardened.
    return OTCRYPTO_NOT_IMPLEMENTED;
  }

  // Check for null label with nonzero length.
  if (kdf_label.data == NULL && kdf_label.len != 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check for null context with nonzero length.
  if (kdf_context.data == NULL && kdf_context.len != 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the private key checksum.
  if (integrity_blinded_key_check(&key_derivation_key) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check non-zero length for keying_material.
  if (required_byte_len == 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Infer the digest size.
  size_t digest_word_len = 0;
  HARDENED_TRY(digest_num_words_from_key_mode(
      key_derivation_key.config.key_mode, &digest_word_len));

  // Ensure that the derived key is a symmetric key masked with XOR and is not
  // supposed to be hardware-backed.
  HARDENED_TRY(keyblob_ensure_xor_masked(keying_material->config));

  // Check `keying_material` key length.
  if (keying_material->config.hw_backed == kHardenedBoolTrue) {
    // The case where `keying_material` is hw_backed is addressed by
    // `otcrypto_hw_backed_key` function in `key_transport.h`.
    return OTCRYPTO_BAD_ARGS;
  } else if (keying_material->config.hw_backed == kHardenedBoolFalse) {
    if (keying_material->config.key_length != required_byte_len ||
        keying_material->keyblob_length !=
            keyblob_num_words(keying_material->config) * sizeof(uint32_t)) {
      return OTCRYPTO_BAD_ARGS;
    }
  } else {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check that the unmasked key length is not too large for HMAC CTR
  // (see NIST SP 800-108r1, section 4.1)
  size_t required_word_len = ceil_div(required_byte_len, sizeof(uint32_t));
  size_t num_iterations = ceil_div(required_word_len, digest_word_len);
  if (launder32(num_iterations) > UINT32_MAX) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_LE(num_iterations, UINT32_MAX);

  // Check if label or context contain 0x00 bytes
  // Since 0x00 is used as the delimiter between label and context
  // there shouldn't be multiple instances of them in input data
  HARDENED_TRY(check_zero_byte(kdf_label));
  HARDENED_TRY(check_zero_byte(kdf_context));

  // Setup
  uint8_t zero = 0x00;
  HARDENED_CHECK_LE(required_byte_len, UINT32_MAX / 8);
  uint32_t required_bit_len = __builtin_bswap32(required_byte_len * 8);

  // Repeatedly call HMAC to generate the derived key based on input data:
  // [i]_2 || Label || 0x00 || Context || [L]_2
  // (see NIST SP 800-108r1, section 4.1)
  // [i]_2 is the binary representation of the counter value
  // [L]_2 is the binary representation of the required bit length
  // The counter value is updated within the loop

  uint32_t keying_material_len =
      required_word_len + digest_word_len - required_word_len % digest_word_len;
  uint32_t keying_material_data[keying_material_len];

  for (uint32_t i = 0; i < num_iterations; i++) {
    otcrypto_hmac_context_t ctx;
    HARDENED_TRY(otcrypto_hmac_init(&ctx, &key_derivation_key));
    uint32_t counter_be = __builtin_bswap32(i + 1);
    HARDENED_TRY(otcrypto_hmac_update(
        &ctx, (otcrypto_const_byte_buf_t){
                  .data = (const unsigned char *const)&counter_be,
                  .len = sizeof(counter_be)}));
    HARDENED_TRY(otcrypto_hmac_update(&ctx, kdf_label));
    HARDENED_TRY(otcrypto_hmac_update(
        &ctx,
        (otcrypto_const_byte_buf_t){.data = (const unsigned char *const)&zero,
                                    .len = sizeof(zero)}));
    HARDENED_TRY(otcrypto_hmac_update(&ctx, kdf_context));
    HARDENED_TRY(otcrypto_hmac_update(
        &ctx, (otcrypto_const_byte_buf_t){
                  .data = (const unsigned char *const)&required_bit_len,
                  .len = sizeof(required_bit_len)}));
    uint32_t *tag_dest = keying_material_data + i * digest_word_len;
    HARDENED_TRY(otcrypto_hmac_final(
        &ctx,
        (otcrypto_word32_buf_t){.data = tag_dest, .len = digest_word_len}));
  }

  // Generate a mask (all-zero for now, since HMAC is unhardened anyway).
  uint32_t mask[digest_word_len];
  memset(mask, 0, sizeof(mask));

  // Construct a blinded key.
  HARDENED_TRY(keyblob_from_key_and_mask(keying_material_data, mask,
                                         keying_material->config,
                                         keying_material->keyblob));

  keying_material->checksum = integrity_blinded_checksum(keying_material);

  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_kdf_kmac(
    const otcrypto_blinded_key_t key_derivation_key,
    otcrypto_kmac_mode_t kmac_mode, const otcrypto_const_byte_buf_t kdf_label,
    const otcrypto_const_byte_buf_t kdf_context, size_t required_byte_len,
    otcrypto_blinded_key_t *keying_material) {
  // Check NULL pointers.
  if (key_derivation_key.keyblob == NULL || keying_material == NULL ||
      keying_material->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check for null label with nonzero length.
  if (kdf_label.data == NULL && kdf_label.len != 0) {
    return OTCRYPTO_BAD_ARGS;
  }
  // Because of KMAC HWIPs prefix limitation, `label` should not exceed
  // `kKmacCustStrMaxSize` bytes.
  if (kdf_label.len > kKmacCustStrMaxSize) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check for null context with nonzero length.
  if (kdf_context.data == NULL && kdf_context.len != 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the private key checksum.
  if (integrity_blinded_key_check(&key_derivation_key) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check `key_len` is supported by KMAC HWIP.
  // The set of supported key sizes is {128, 192, 256, 384, 512).
  HARDENED_TRY(kmac_key_length_check(key_derivation_key.config.key_length));

  kmac_blinded_key_t kmac_key = {
      .share0 = NULL,
      .share1 = NULL,
      .hw_backed = key_derivation_key.config.hw_backed,
      .len = key_derivation_key.config.key_length,
  };
  // Validate key length of `key_derivation_key`.
  if (key_derivation_key.config.hw_backed == kHardenedBoolTrue) {
    // Check that 1) key size matches sideload port size, 2) keyblob length
    // matches diversification length.
    if (keyblob_share_num_words(key_derivation_key.config) * sizeof(uint32_t) !=
        kKmacSideloadKeyLength / 8) {
      return OTCRYPTO_BAD_ARGS;
    }
    // Configure keymgr with diversification input and then generate the
    // sideload key.
    keymgr_diversification_t diversification;
    // Diversification call also checks that `key_derivation_key.keyblob_length`
    // is 8 words long.
    HARDENED_TRY(keyblob_to_keymgr_diversification(&key_derivation_key,
                                                   &diversification));
    HARDENED_TRY(keymgr_generate_key_kmac(diversification));
  } else if (key_derivation_key.config.hw_backed == kHardenedBoolFalse) {
    if (key_derivation_key.keyblob_length !=
        keyblob_num_words(key_derivation_key.config) * sizeof(uint32_t)) {
      return OTCRYPTO_BAD_ARGS;
    }
    HARDENED_TRY(keyblob_to_shares(&key_derivation_key, &kmac_key.share0,
                                   &kmac_key.share1));
  } else {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check non-zero length for keying_material.
  if (required_byte_len == 0) {
    return OTCRYPTO_BAD_ARGS;
  }
  // At the moment, `kmac_kmac_128/256` only supports word-sized digest lenghts.
  if (required_byte_len % sizeof(uint32_t) != 0) {
    return OTCRYPTO_NOT_IMPLEMENTED;
  }

  // Check `keying_material` key length.
  if (keying_material->config.hw_backed == kHardenedBoolTrue) {
    // The case where `keying_material` is hw_backed is addressed by
    // `otcrypto_hw_backed_key` function in `key_transport.h`.
    return OTCRYPTO_BAD_ARGS;
  } else if (keying_material->config.hw_backed == kHardenedBoolFalse) {
    if (keying_material->config.key_length != required_byte_len ||
        keying_material->keyblob_length !=
            keyblob_num_words(keying_material->config) * sizeof(uint32_t)) {
      return OTCRYPTO_BAD_ARGS;
    }
  } else {
    return OTCRYPTO_BAD_ARGS;
  }

  if (kmac_mode == kOtcryptoKmacModeKmac128) {
    // Check if `key_mode` of the key derivation key matches `kmac_mode`.
    if (key_derivation_key.config.key_mode != kOtcryptoKeyModeKdfKmac128) {
      return OTCRYPTO_BAD_ARGS;
    }
    // No need to further check key size against security level because
    // `kmac_key_length_check` ensures that the key is at least 128-bit.
    HARDENED_TRY(kmac_kmac_128(&kmac_key, kdf_context.data, kdf_context.len,
                               kdf_label.data, kdf_label.len,
                               keying_material->keyblob,
                               required_byte_len / sizeof(uint32_t)));
  } else if (kmac_mode == kOtcryptoKmacModeKmac256) {
    // Check if `key_mode` of the key derivation key matches `kmac_mode`.
    if (key_derivation_key.config.key_mode != kOtcryptoKeyModeKdfKmac256) {
      return OTCRYPTO_BAD_ARGS;
    }
    // Check that key size matches the security strength. It should be at least
    // 256-bit.
    if (key_derivation_key.config.key_length < 256 / 8) {
      return OTCRYPTO_BAD_ARGS;
    }
    HARDENED_TRY(kmac_kmac_256(&kmac_key, kdf_context.data, kdf_context.len,
                               kdf_label.data, kdf_label.len,
                               keying_material->keyblob,
                               required_byte_len / sizeof(uint32_t)));
  } else {
    return OTCRYPTO_BAD_ARGS;
  }

  keying_material->checksum = integrity_blinded_checksum(keying_material);

  if (key_derivation_key.config.hw_backed == kHardenedBoolTrue) {
    HARDENED_TRY(keymgr_sideload_clear_kmac());
  } else if (key_derivation_key.config.hw_backed != kHardenedBoolFalse) {
    return OTCRYPTO_BAD_ARGS;
  }

  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_kdf_hkdf(const otcrypto_blinded_key_t ikm,
                                    otcrypto_const_byte_buf_t salt,
                                    otcrypto_const_byte_buf_t info,
                                    otcrypto_blinded_key_t *okm) {
  // Infer the digest length.
  size_t digest_wordlen;
  HARDENED_TRY(
      digest_num_words_from_key_mode(ikm.config.key_mode, &digest_wordlen));
  size_t digest_bytelen = digest_wordlen * sizeof(uint32_t);

  // Construct a blinded key struct for the intermediate key.
  otcrypto_key_config_t prk_config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = ikm.config.key_mode,
      .key_length = digest_bytelen,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  size_t keyblob_wordlen = keyblob_num_words(prk_config);
  uint32_t keyblob[keyblob_wordlen];
  otcrypto_blinded_key_t prk = {
      .config = prk_config,
      .keyblob = keyblob,
      .keyblob_length = sizeof(keyblob),
  };

  // Call extract and expand.
  HARDENED_TRY(otcrypto_kdf_hkdf_extract(ikm, salt, &prk));
  return otcrypto_kdf_hkdf_expand(prk, info, okm);
}

/**
 * Check that an HKDF pseudo-random key is correctly configured.
 *
 * Ensures that the key mode, length, and allocated keyblob length are suitable
 * for an HKDF pseudo-random key (i.e. the input for extract and the output for
 * expand). Does not dereference the keyblob, so it is safe to call this before
 * the keyblob is initialized.
 *
 * @param digest_words Length of the hash digest in 32-bit words.
 * @param prk Pseudo-random key struct to check.
 * @return OK if the PRK is acceptable, otherwise OTCRYPTO_BAD_ARGS.
 */
static status_t hkdf_check_prk(size_t digest_words,
                               const otcrypto_blinded_key_t *prk) {
  if (launder32(prk->config.key_mode) >> 16 != kOtcryptoKeyTypeHmac) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(prk->config.key_mode >> 16, kOtcryptoKeyTypeHmac);

  // PRK should be the same length as the digest.
  size_t digest_bytelen = digest_words * sizeof(uint32_t);
  if (launder32(prk->config.key_length) != digest_bytelen) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(prk->config.key_length, digest_bytelen);

  // Check the keyblob length.
  size_t keyblob_bytelen = keyblob_num_words(prk->config) * sizeof(uint32_t);
  if (launder32(prk->keyblob_length) != keyblob_bytelen) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(prk->keyblob_length, keyblob_bytelen);

  // Ensure that the PRK is a symmetric key masked with XOR and is not supposed
  // to be hardware-backed.
  HARDENED_TRY(keyblob_ensure_xor_masked(prk->config));

  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_kdf_hkdf_extract(const otcrypto_blinded_key_t ikm,
                                            otcrypto_const_byte_buf_t salt,
                                            otcrypto_blinded_key_t *prk) {
  // Check for null pointers.
  if (ikm.keyblob == NULL || prk == NULL || prk->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (salt.data == NULL && salt.len != 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the private key checksum.
  if (integrity_blinded_key_check(&ikm) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (launder32(ikm.config.security_level) != kOtcryptoKeySecurityLevelLow ||
      launder32(prk->config.security_level) != kOtcryptoKeySecurityLevelLow) {
    // The underlying HMAC implementation is not currently hardened.
    return OTCRYPTO_NOT_IMPLEMENTED;
  }
  HARDENED_CHECK_EQ(ikm.config.security_level, kOtcryptoKeySecurityLevelLow);
  HARDENED_CHECK_EQ(prk->config.security_level, kOtcryptoKeySecurityLevelLow);

  // Ensure the key modes match.
  if (launder32(prk->config.key_mode) != launder32(ikm.config.key_mode)) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(prk->config.key_mode, ikm.config.key_mode);

  // Infer the digest size. This step also ensures that the key mode is
  // supported.
  size_t digest_words = 0;
  HARDENED_TRY(
      digest_num_words_from_key_mode(ikm.config.key_mode, &digest_words));

  // Validate the PRK configuration.
  HARDENED_TRY(hkdf_check_prk(digest_words, prk));

  // Copy the salt into a 32-bit aligned buffer. If the salt is empty, replace
  // it with a string of `hashLen` zeroes as specified in RFC 5869.
  size_t salt_bytelen =
      (salt.len == 0) ? digest_words * sizeof(uint32_t) : salt.len;
  size_t salt_wordlen = ceil_div(salt_bytelen, sizeof(uint32_t));
  uint32_t salt_aligned_data[salt_wordlen];
  memset(salt_aligned_data, 0, sizeof(salt_aligned_data));
  if (salt.len > 0) {
    memcpy(salt_aligned_data, salt.data, salt.len);
  }

  // The extract stage uses `salt` as the key and the input key as the message.
  // We therefore need to unmask the key and package the salt in a blinded key
  // struct.

  // Unmask the input key.
  uint32_t *ikm_share0;
  uint32_t *ikm_share1;
  HARDENED_TRY(keyblob_to_shares(&ikm, &ikm_share0, &ikm_share1));
  uint32_t unmasked_ikm_data[keyblob_share_num_words(ikm.config)];
  for (size_t i = 0; i < ARRAYSIZE(unmasked_ikm_data); i++) {
    unmasked_ikm_data[i] = ikm_share0[i] ^ ikm_share1[i];
  }
  otcrypto_const_byte_buf_t unmasked_ikm = {
      .data = (unsigned char *)unmasked_ikm_data,
      .len = ikm.config.key_length,
  };

  // Package the salt value in a blinded key, using an all-zero mask because
  // the salt is not actually secret.
  uint32_t salt_mask[ARRAYSIZE(salt_aligned_data)];
  memset(salt_mask, 0, sizeof(salt_mask));
  otcrypto_key_config_t salt_key_config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = ikm.config.key_mode,
      .key_length = salt_bytelen,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  uint32_t salt_keyblob[keyblob_num_words(salt_key_config)];
  TRY(keyblob_from_key_and_mask(salt_aligned_data, salt_mask, salt_key_config,
                                salt_keyblob));
  otcrypto_blinded_key_t salt_key = {
      .config = salt_key_config,
      .keyblob = salt_keyblob,
      .keyblob_length = sizeof(salt_keyblob),
  };

  // Call HMAC(salt, IKM).
  uint32_t tag_data[digest_words];
  otcrypto_word32_buf_t tag = {.data = tag_data, .len = ARRAYSIZE(tag_data)};
  HARDENED_TRY(otcrypto_hmac(&salt_key, unmasked_ikm, tag));

  // Construct the blinded keyblob for PRK (with an all-zero mask for now
  // because HMAC is unhardened anyway).
  uint32_t prk_mask[digest_words];
  memset(prk_mask, 0, sizeof(prk_mask));
  HARDENED_TRY(
      keyblob_from_key_and_mask(tag_data, prk_mask, prk->config, prk->keyblob));
  prk->checksum = integrity_blinded_checksum(prk);
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_kdf_hkdf_expand(const otcrypto_blinded_key_t prk,
                                           otcrypto_const_byte_buf_t info,
                                           otcrypto_blinded_key_t *okm) {
  if (okm == NULL || okm->keyblob == NULL || prk.keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (info.data == NULL && info.len != 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (launder32(okm->config.security_level) != kOtcryptoKeySecurityLevelLow ||
      launder32(prk.config.security_level) != kOtcryptoKeySecurityLevelLow) {
    // The underlying HMAC implementation is not currently hardened.
    return OTCRYPTO_NOT_IMPLEMENTED;
  }

  // Infer the digest size.
  size_t digest_words = 0;
  HARDENED_TRY(
      digest_num_words_from_key_mode(prk.config.key_mode, &digest_words));

  // Check the PRK configuration.
  HARDENED_TRY(hkdf_check_prk(digest_words, &prk));

  // Ensure that the derived key is a symmetric key masked with XOR and is not
  // supposed to be hardware-backed.
  HARDENED_TRY(keyblob_ensure_xor_masked(okm->config));

  // Check the keyblob length.
  size_t keyblob_bytelen = keyblob_num_words(okm->config) * sizeof(uint32_t);
  if (launder32(okm->keyblob_length) != keyblob_bytelen) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(okm->keyblob_length, keyblob_bytelen);

  // Check that the unmasked key length is not too large for HKDF (see RFC
  // 5869, section 2.3).
  size_t okm_bytelen = okm->config.key_length;
  size_t okm_wordlen = ceil_div(okm_bytelen, sizeof(uint32_t));
  size_t num_iterations = ceil_div(okm_wordlen, digest_words);
  if (launder32(num_iterations) > 255) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_LE(num_iterations, 255);

  // Create a buffer that holds `info` and a one-byte counter.
  uint8_t info_and_counter_data[info.len + 1];
  memcpy(info_and_counter_data, info.data, info.len);
  info_and_counter_data[info.len] = 0x00;
  otcrypto_const_byte_buf_t info_and_counter = {
      .data = info_and_counter_data,
      .len = sizeof(info_and_counter_data),
  };

  // Repeatedly call HMAC to generate the derived key (see RFC 5869, section
  // 2.3):
  uint32_t okm_data[okm_wordlen];
  uint32_t *t_data = okm_data;
  for (uint8_t i = 0; i < num_iterations; i++) {
    info_and_counter_data[info.len] = i + 1;
    otcrypto_hmac_context_t ctx;
    HARDENED_TRY(otcrypto_hmac_init(&ctx, &prk));
    if (launder32(i) != 0) {
      otcrypto_const_byte_buf_t t_bytes = {
          .data = (unsigned char *)t_data,
          .len = digest_words * sizeof(uint32_t),
      };
      HARDENED_TRY(otcrypto_hmac_update(&ctx, t_bytes));
      t_data += digest_words;
    }
    HARDENED_TRY(otcrypto_hmac_update(&ctx, info_and_counter));
    otcrypto_word32_buf_t t_words = {
        .data = t_data,
        .len = digest_words,
    };
    HARDENED_TRY(otcrypto_hmac_final(&ctx, t_words));
  }

  // Generate a mask (all-zero for now, since HMAC is unhardened anyway).
  uint32_t mask[digest_words];
  memset(mask, 0, sizeof(mask));

  // Construct a blinded key.
  HARDENED_TRY(
      keyblob_from_key_and_mask(okm_data, mask, okm->config, okm->keyblob));
  okm->checksum = integrity_blinded_checksum(okm);
  return OTCRYPTO_OK;
}
