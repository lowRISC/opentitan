// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/cmac_kdf.h"

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/crypto/drivers/aes.h"
#include "sw/device/lib/crypto/impl/cmvp.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/state.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/cmac.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/integrity.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('c', 'k', 'f')

/**
 * Check if the string contains a 0x00 byte.
 *
 * @param buffer Inspected string.
 * @return OK or error.
 */
static status_t check_zero_byte(const otcrypto_const_byte_buf_t *buffer) {
  for (size_t i = 0; i < buffer->len; i++) {
    if (buffer->data[i] == 0x00) {
      return OTCRYPTO_BAD_ARGS;
    }
  }
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_cmac_kdf(
    const otcrypto_blinded_key_t *key_derivation_key,
    const otcrypto_const_byte_buf_t *label,
    const otcrypto_const_byte_buf_t *context,
    otcrypto_blinded_key_t *output_key_material) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_CMAC_KDF);
  OTCRYPTO_LOCKED_STATE_CHECK();
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  // Check NULL pointers.
  if (output_key_material == NULL || output_key_material->keyblob == NULL ||
      key_derivation_key == NULL || key_derivation_key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check for null label with nonzero length.
  if (label == NULL || (label->data == NULL && label->len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check for null context with nonzero length.
  if (context == NULL || (context->data == NULL && context->len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  // Check the key derivation key checksum.
  if (launder32(otcrypto_integrity_blinded_key_check(key_derivation_key)) !=
      kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(otcrypto_integrity_blinded_key_check(key_derivation_key),
                    kHardenedBoolTrue);

  // Check the key mode.
  if (launder32(key_derivation_key->config.key_mode) !=
      kOtcryptoKeyModeAesCmac) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(key_derivation_key->config.key_mode,
                    kOtcryptoKeyModeAesCmac);

  // Check non-zero length for output_key_material.
  if (output_key_material->config.key_length == 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Ensure that the derived key is a symmetric key masked with XOR and is not
  // supposed to be hardware-backed.
  HARDENED_TRY(keyblob_ensure_xor_masked(output_key_material->config));

  // Check the keyblob length.
  size_t keyblob_bytelen =
      keyblob_num_words(output_key_material->config) * sizeof(uint32_t);
  if (launder32(output_key_material->keyblob_length) != keyblob_bytelen) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(output_key_material->keyblob_length, keyblob_bytelen);

  // Check that the unmasked key length is not too large for CMAC CTR
  // (see NIST SP 800-108r1, section 4.1).
  size_t required_byte_len = output_key_material->config.key_length;
  size_t required_word_len = ceil_div(required_byte_len, sizeof(uint32_t));
  size_t num_iterations = ceil_div(required_word_len, kAesBlockNumWords);
  if (launder32(required_byte_len) > UINT32_MAX / 8) {
    // COVERAGE (FI CM) Redundant check; keyblob_ensure_xor_masked already
    // bounds key_length.
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_LE(required_byte_len, UINT32_MAX / 8);
  uint32_t required_bit_len = __builtin_bswap32(required_byte_len * 8);

  // Check if label contains 0x00 bytes. Since 0x00 is used as the
  // delimiter between label and context, there shouldn't be multiple instances
  // of it in the label data.
  HARDENED_TRY(check_zero_byte(label));

  // Setup
  uint8_t zero = 0x00;
  size_t share_word_len = keyblob_share_num_words(output_key_material->config);
  HARDENED_CHECK_EQ(required_word_len, share_word_len);
  HARDENED_CHECK_GT(required_word_len, 0);
  uint32_t *share0_ptr = output_key_material->keyblob;
  uint32_t *share1_ptr = output_key_material->keyblob + share_word_len;
  size_t words_written = 0;

  // Repeatedly call CMAC to generate the derived key based on input data:
  // [i]_2 || Label || 0x00 || Context || [L]_2
  // (see NIST SP 800-108r1, section 4.1)
  // [i]_2 is the binary representation of the counter value
  // [L]_2 is the binary representation of the required bit length
  // The counter value is updated within the loop.
  uint32_t tag_data[kAesBlockNumWords];

  for (uint32_t i = 0; i < num_iterations; i++) {
    otcrypto_cmac_context_t ctx;
    HARDENED_TRY(otcrypto_cmac_init(&ctx, key_derivation_key));
    uint32_t counter_be = __builtin_bswap32(i + 1);
    otcrypto_const_byte_buf_t counter_be_buf = OTCRYPTO_MAKE_BUF(
        otcrypto_const_byte_buf_t, (const unsigned char *const)&counter_be,
        sizeof(counter_be));
    HARDENED_TRY(otcrypto_cmac_update(&ctx, &counter_be_buf));
    HARDENED_TRY(otcrypto_cmac_update(&ctx, label));
    otcrypto_const_byte_buf_t zero_buf =
        OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t,
                          (const unsigned char *const)&zero, sizeof(zero));
    HARDENED_TRY(otcrypto_cmac_update(&ctx, &zero_buf));
    HARDENED_TRY(otcrypto_cmac_update(&ctx, context));
    otcrypto_const_byte_buf_t required_bit_len_buf =
        OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t,
                          (const unsigned char *const)&required_bit_len,
                          sizeof(required_bit_len));
    HARDENED_TRY(otcrypto_cmac_update(&ctx, &required_bit_len_buf));
    otcrypto_word32_buf_t tag_buf =
        OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, tag_data, kAesBlockNumWords);
    HARDENED_TRY(otcrypto_cmac_final(&ctx, &tag_buf));

    size_t words_to_copy = kAesBlockNumWords;
    if (words_written + kAesBlockNumWords > required_word_len) {
      words_to_copy = required_word_len - words_written;
    }

    uint32_t mask_data[kAesBlockNumWords];
    HARDENED_TRY(hardened_memshred(mask_data, words_to_copy));

    uint32_t share0_data[kAesBlockNumWords];
    HARDENED_TRY(hardened_xor(tag_data, mask_data, words_to_copy, share0_data));

    HARDENED_TRY(hardened_memcpy(share0_ptr + words_written, share0_data,
                                 words_to_copy));
    HARDENED_TRY(
        hardened_memcpy(share1_ptr + words_written, mask_data, words_to_copy));

    words_written += words_to_copy;
  }
  HARDENED_CHECK_EQ(words_written, required_word_len);
  HARDENED_CHECK_GT(words_written, 0);

  HARDENED_TRY(hardened_memshred(tag_data, kAesBlockNumWords));

  output_key_material->checksum =
      otcrypto_integrity_blinded_checksum(output_key_material);

  return otcrypto_eval_exit(OTCRYPTO_OK);
}
