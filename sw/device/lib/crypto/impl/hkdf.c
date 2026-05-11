// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/hkdf.h"

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/crypto/drivers/hmac.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/hkdf.h"
#include "sw/device/lib/crypto/include/hmac.h"
#include "sw/device/lib/crypto/include/integrity.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('h', 'k', 'd')

enum {
  // Maximum length for the salt in 32-bit words (512 bytes).
  kHkdfMaxSaltWords = 128,
  // Maximum length for the input key material (IKM) in 32-bit words (512
  // bytes).
  kHkdfMaxIkmWords = 128,
};

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
  size_t digest_words_set = launder32(0);
  switch (launder32(key_mode)) {
    case kOtcryptoKeyModeHmacSha256:
      *digest_words = 256 / 32;
      digest_words_set =
          launder32(digest_words_set) | kOtcryptoKeyModeHmacSha256;
      break;
    case kOtcryptoKeyModeHmacSha384:
      *digest_words = 384 / 32;
      digest_words_set =
          launder32(digest_words_set) | kOtcryptoKeyModeHmacSha384;
      break;
    case kOtcryptoKeyModeHmacSha512:
      *digest_words = 512 / 32;
      digest_words_set =
          launder32(digest_words_set) | kOtcryptoKeyModeHmacSha512;
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }
  // Check if we landed in the correct case statement. Use ORs for this to
  // avoid that multiple cases were executed.
  HARDENED_CHECK_EQ(launder32(digest_words_set), key_mode);
  HARDENED_CHECK_NE(*digest_words, 0);
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_hkdf(const otcrypto_blinded_key_t *ikm,
                                const otcrypto_const_byte_buf_t *salt,
                                const otcrypto_const_byte_buf_t *info,
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
  uint32_t keyblob[kHmacMaxDigestWords * 2];
  otcrypto_blinded_key_t prk = {
      .config = prk_config,
      .keyblob = keyblob,
      .keyblob_length = keyblob_wordlen * sizeof(uint32_t),
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
  HARDENED_TRY(keyblob_ensure_xor_masked(prk->config));

  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_hkdf_extract(const otcrypto_blinded_key_t *ikm,
                                        const otcrypto_const_byte_buf_t *salt,
                                        otcrypto_blinded_key_t *prk) {
  // Check for null pointers.
  if (ikm == NULL || ikm->keyblob == NULL || prk == NULL ||
      prk->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (salt == NULL || (salt->data == NULL && salt->len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the private key checksum.
  if (launder32(otcrypto_integrity_blinded_key_check(ikm)) !=
      kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }

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
      (salt->len == 0) ? digest_words * sizeof(uint32_t) : salt->len;
  size_t salt_wordlen = ceil_div(salt_bytelen, sizeof(uint32_t));

  if (salt_wordlen > kHkdfMaxSaltWords) {
    return OTCRYPTO_BAD_ARGS;
  }
  uint32_t salt_aligned_data[kHkdfMaxSaltWords];
  memset(salt_aligned_data, 0, salt_wordlen * sizeof(uint32_t));
  if (salt->len > 0) {
    memcpy(salt_aligned_data, salt->data, salt->len);
  }

  // The extract stage uses `salt` as the key and the input key as the message.
  // We therefore need to unmask the key and package the salt in a blinded key
  // struct.

  // Unmask the input key.
  size_t unmasked_ikm_wordlen = keyblob_share_num_words(ikm->config);
  if (unmasked_ikm_wordlen > kHkdfMaxIkmWords) {
    return OTCRYPTO_BAD_ARGS;
  }
  uint32_t unmasked_ikm_data[kHkdfMaxIkmWords];
  HARDENED_TRY(
      keyblob_key_unmask(ikm, unmasked_ikm_wordlen, unmasked_ikm_data));
  otcrypto_const_byte_buf_t unmasked_ikm = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, (unsigned char *)unmasked_ikm_data,
      ikm->config.key_length);

  // Package the salt value in a blinded key, using an all-zero mask because
  // the salt is not actually secret.
  uint32_t salt_mask[kHkdfMaxSaltWords];
  memset(salt_mask, 0, salt_wordlen * sizeof(uint32_t));
  otcrypto_key_config_t salt_key_config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = ikm->config.key_mode,
      .key_length = salt_bytelen,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  uint32_t salt_keyblob[keyblob_num_words(salt_key_config)];
  HARDENED_TRY(keyblob_from_key_and_mask(salt_aligned_data, salt_mask,
                                         salt_key_config, salt_keyblob));
  otcrypto_blinded_key_t salt_key = {
      .config = salt_key_config,
      .keyblob = salt_keyblob,
      .keyblob_length = sizeof(salt_keyblob),
  };
  salt_key.checksum = otcrypto_integrity_blinded_checksum(&salt_key);

  // Call HMAC(salt, IKM).
  uint32_t tag_data[kHmacMaxDigestWords];
  otcrypto_word32_buf_t tag =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, tag_data, digest_words);
  HARDENED_TRY(otcrypto_hmac(&salt_key, &unmasked_ikm, &tag));

  // Mask the PRK
  uint32_t prk_mask[kHmacMaxDigestWords];
  HARDENED_TRY(hardened_memshred(prk_mask, digest_words));

  HARDENED_TRY(
      keyblob_from_key_and_mask(tag_data, prk_mask, prk->config, prk->keyblob));

  // Wipe the sensitive buffers
  HARDENED_TRY(hardened_memshred(unmasked_ikm_data, unmasked_ikm_wordlen));
  HARDENED_TRY(hardened_memshred(tag_data, digest_words));

  prk->checksum = otcrypto_integrity_blinded_checksum(prk);
  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_hkdf_expand(const otcrypto_blinded_key_t *prk,
                                       const otcrypto_const_byte_buf_t *info,
                                       otcrypto_blinded_key_t *okm) {
  if (okm == NULL || okm->keyblob == NULL || prk == NULL ||
      prk->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (info == NULL || (info->data == NULL && info->len != 0)) {
    return OTCRYPTO_BAD_ARGS;
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

  // Repeatedly call HMAC to generate the derived key (see RFC 5869,
  // section 2.3).
  uint32_t *share0_ptr = okm->keyblob;
  uint32_t *share1_ptr = okm->keyblob + keyblob_share_num_words(okm->config);
  size_t words_written = 0;

  // Array to hold T(i) from the previous loop iteration.
  uint32_t prev_t[kHmacMaxDigestWords];

  for (uint8_t i = 0; i < num_iterations; i++) {
    otcrypto_hmac_context_t ctx;
    HARDENED_TRY(otcrypto_hmac_init(&ctx, prk));
    if (launder32(i) != 0) {
      otcrypto_const_byte_buf_t t_bytes =
          OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, (unsigned char *)prev_t,
                            digest_words * sizeof(uint32_t));
      HARDENED_TRY(otcrypto_hmac_update(&ctx, &t_bytes));
    }

    HARDENED_TRY(otcrypto_hmac_update(&ctx, info));

    uint8_t counter_val = i + 1;
    otcrypto_const_byte_buf_t counter_buf =
        OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, &counter_val, 1);
    HARDENED_TRY(otcrypto_hmac_update(&ctx, &counter_buf));

    uint32_t tag_data[kHmacMaxDigestWords];
    otcrypto_word32_buf_t t_words =
        OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, tag_data, digest_words);
    HARDENED_TRY(otcrypto_hmac_final(&ctx, &t_words));

    memcpy(prev_t, tag_data, digest_words * sizeof(uint32_t));

    size_t words_to_copy = digest_words;
    if (words_written + digest_words > okm_wordlen) {
      words_to_copy = okm_wordlen - words_written;
    }

    uint32_t mask_data[kHmacMaxDigestWords];
    HARDENED_TRY(hardened_memshred(mask_data, words_to_copy));

    uint32_t share0_data[kHmacMaxDigestWords];
    HARDENED_TRY(hardened_xor(tag_data, mask_data, words_to_copy, share0_data));

    HARDENED_TRY(hardened_memcpy(share0_ptr + words_written, share0_data,
                                 words_to_copy));
    HARDENED_TRY(
        hardened_memcpy(share1_ptr + words_written, mask_data, words_to_copy));

    words_written += words_to_copy;
  }

  // Manually compute and assign the checksum
  okm->checksum = otcrypto_integrity_blinded_checksum(okm);
  return otcrypto_eval_exit(OTCRYPTO_OK);
}
