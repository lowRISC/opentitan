// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/kdf_ctr.h"

#include "sw/device/lib/base/math.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/hmac.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('c', 'k', 'd')

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

otcrypto_status_t otcrypto_kdf_ctr_hmac(
    const otcrypto_blinded_key_t *key_derivation_key,
    const otcrypto_const_byte_buf_t label,
    const otcrypto_const_byte_buf_t context,
    otcrypto_blinded_key_t *output_key_material) {
  // Check NULL pointers.
  if (output_key_material == NULL || output_key_material->keyblob == NULL ||
      key_derivation_key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (launder32(output_key_material->config.security_level) !=
          kOtcryptoKeySecurityLevelLow ||
      launder32(key_derivation_key->config.security_level) !=
          kOtcryptoKeySecurityLevelLow) {
    // The underlying HMAC implementation is not currently hardened.
    return OTCRYPTO_NOT_IMPLEMENTED;
  }

  // Check for null label with nonzero length.
  if (label.data == NULL && label.len != 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check for null context with nonzero length.
  if (context.data == NULL && context.len != 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the private key checksum.
  if (integrity_blinded_key_check(key_derivation_key) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check non-zero length for output_key_material.
  if (output_key_material->config.key_length == 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Infer the digest size.
  size_t digest_word_len = 0;
  HARDENED_TRY(digest_num_words_from_key_mode(
      key_derivation_key->config.key_mode, &digest_word_len));

  // Ensure that the derived key is a symmetric key masked with XOR and is not
  // supposed to be hardware-backed.
  HARDENED_TRY(keyblob_ensure_xor_masked(output_key_material->config));

  // Check `output_key_material` key length.
  if (output_key_material->config.hw_backed == kHardenedBoolTrue) {
    // The case where `output_key_material` is hw_backed is addressed by
    // `otcrypto_hw_backed_key` function in `key_transport.h`.
    return OTCRYPTO_BAD_ARGS;
  } else if (output_key_material->config.hw_backed == kHardenedBoolFalse) {
    if (output_key_material->keyblob_length !=
        keyblob_num_words(output_key_material->config) * sizeof(uint32_t)) {
      return OTCRYPTO_BAD_ARGS;
    }
  } else {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check that the unmasked key length is not too large for HMAC CTR
  // (see NIST SP 800-108r1, section 4.1)
  size_t required_byte_len = output_key_material->config.key_length;
  size_t required_word_len = ceil_div(required_byte_len, sizeof(uint32_t));
  size_t num_iterations = ceil_div(required_word_len, digest_word_len);
  if (launder32(num_iterations) > UINT32_MAX ||
      launder32(required_byte_len) > UINT32_MAX / 8) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_LE(num_iterations, UINT32_MAX);
  HARDENED_CHECK_LE(required_byte_len, UINT32_MAX / 8);
  uint32_t required_bit_len = __builtin_bswap32(required_byte_len * 8);

  // Check if label or context contain 0x00 bytes
  // Since 0x00 is used as the delimiter between label and context
  // there shouldn't be multiple instances of them in input data
  HARDENED_TRY(check_zero_byte(label));
  HARDENED_TRY(check_zero_byte(context));

  // Setup
  uint8_t zero = 0x00;

  // Repeatedly call HMAC to generate the derived key based on input data:
  // [i]_2 || Label || 0x00 || Context || [L]_2
  // (see NIST SP 800-108r1, section 4.1)
  // [i]_2 is the binary representation of the counter value
  // [L]_2 is the binary representation of the required bit length
  // The counter value is updated within the loop

  uint32_t output_key_material_len =
      required_word_len + digest_word_len - required_word_len % digest_word_len;
  uint32_t output_key_material_data[output_key_material_len];

  for (uint32_t i = 0; i < num_iterations; i++) {
    otcrypto_hmac_context_t ctx;
    HARDENED_TRY(otcrypto_hmac_init(&ctx, key_derivation_key));
    uint32_t counter_be = __builtin_bswap32(i + 1);
    HARDENED_TRY(otcrypto_hmac_update(
        &ctx, (otcrypto_const_byte_buf_t){
                  .data = (const unsigned char *const)&counter_be,
                  .len = sizeof(counter_be)}));
    HARDENED_TRY(otcrypto_hmac_update(&ctx, label));
    HARDENED_TRY(otcrypto_hmac_update(
        &ctx,
        (otcrypto_const_byte_buf_t){.data = (const unsigned char *const)&zero,
                                    .len = sizeof(zero)}));
    HARDENED_TRY(otcrypto_hmac_update(&ctx, context));
    HARDENED_TRY(otcrypto_hmac_update(
        &ctx, (otcrypto_const_byte_buf_t){
                  .data = (const unsigned char *const)&required_bit_len,
                  .len = sizeof(required_bit_len)}));
    uint32_t *tag_dest = output_key_material_data + i * digest_word_len;
    HARDENED_TRY(otcrypto_hmac_final(
        &ctx,
        (otcrypto_word32_buf_t){.data = tag_dest, .len = digest_word_len}));
  }

  // Generate a mask (all-zero for now, since HMAC is unhardened anyway).
  uint32_t mask[digest_word_len];
  memset(mask, 0, sizeof(mask));

  // Construct a blinded key.
  HARDENED_TRY(keyblob_from_key_and_mask(output_key_material_data, mask,
                                         output_key_material->config,
                                         output_key_material->keyblob));

  output_key_material->checksum =
      integrity_blinded_checksum(output_key_material);

  return OTCRYPTO_OK;
}
