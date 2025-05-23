// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/hkdf.h"

#include "sw/device/lib/base/math.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/hkdf.h"
#include "sw/device/lib/crypto/include/hmac.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('h', 'k', 'd')

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

otcrypto_status_t otcrypto_hkdf(const otcrypto_blinded_key_t *ikm,
                                otcrypto_const_byte_buf_t salt,
                                otcrypto_const_byte_buf_t info,
                                otcrypto_blinded_key_t *okm) {
  // Infer the digest length.
  size_t digest_wordlen;
  HARDENED_TRY(
      digest_num_words_from_key_mode(ikm->config.key_mode, &digest_wordlen));
  size_t digest_bytelen = digest_wordlen * sizeof(uint32_t);

  // Construct a blinded key struct for the intermediate key.
  otcrypto_key_config_t prk_config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = ikm->config.key_mode,
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
  HARDENED_TRY(otcrypto_hkdf_extract(ikm, salt, &prk));
  return otcrypto_hkdf_expand(&prk, info, okm);
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
  return keyblob_ensure_xor_masked(prk->config);
}

otcrypto_status_t otcrypto_hkdf_extract(const otcrypto_blinded_key_t *ikm,
                                        otcrypto_const_byte_buf_t salt,
                                        otcrypto_blinded_key_t *prk) {
  // Check for null pointers.
  if (ikm->keyblob == NULL || prk == NULL || prk->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (salt.data == NULL && salt.len != 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the private key checksum.
  if (integrity_blinded_key_check(ikm) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (launder32(ikm->config.security_level) != kOtcryptoKeySecurityLevelLow ||
      launder32(prk->config.security_level) != kOtcryptoKeySecurityLevelLow) {
    // The underlying HMAC implementation is not currently hardened.
    return OTCRYPTO_NOT_IMPLEMENTED;
  }
  HARDENED_CHECK_EQ(ikm->config.security_level, kOtcryptoKeySecurityLevelLow);
  HARDENED_CHECK_EQ(prk->config.security_level, kOtcryptoKeySecurityLevelLow);

  // Ensure the key modes match.
  if (launder32(prk->config.key_mode) != launder32(ikm->config.key_mode)) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(prk->config.key_mode, ikm->config.key_mode);

  // Infer the digest size. This step also ensures that the key mode is
  // supported.
  size_t digest_words = 0;
  HARDENED_TRY(
      digest_num_words_from_key_mode(ikm->config.key_mode, &digest_words));

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
  uint32_t unmasked_ikm_data[keyblob_share_num_words(ikm->config)];
  HARDENED_TRY(
      keyblob_key_unmask(ikm, ARRAYSIZE(unmasked_ikm_data), unmasked_ikm_data));
  otcrypto_const_byte_buf_t unmasked_ikm = {
      .data = (unsigned char *)unmasked_ikm_data,
      .len = ikm->config.key_length,
  };

  // Package the salt value in a blinded key, using an all-zero mask because
  // the salt is not actually secret.
  uint32_t salt_mask[ARRAYSIZE(salt_aligned_data)];
  memset(salt_mask, 0, sizeof(salt_mask));
  otcrypto_key_config_t salt_key_config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = ikm->config.key_mode,
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
  salt_key.checksum = integrity_blinded_checksum(&salt_key);

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

otcrypto_status_t otcrypto_hkdf_expand(const otcrypto_blinded_key_t *prk,
                                       otcrypto_const_byte_buf_t info,
                                       otcrypto_blinded_key_t *okm) {
  if (okm == NULL || okm->keyblob == NULL || prk->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (info.data == NULL && info.len != 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (launder32(okm->config.security_level) != kOtcryptoKeySecurityLevelLow ||
      launder32(prk->config.security_level) != kOtcryptoKeySecurityLevelLow) {
    // The underlying HMAC implementation is not currently hardened.
    return OTCRYPTO_NOT_IMPLEMENTED;
  }

  // Infer the digest size.
  size_t digest_words = 0;
  HARDENED_TRY(
      digest_num_words_from_key_mode(prk->config.key_mode, &digest_words));

  // Check the PRK configuration.
  HARDENED_TRY(hkdf_check_prk(digest_words, prk));

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
    HARDENED_TRY(otcrypto_hmac_init(&ctx, prk));
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
