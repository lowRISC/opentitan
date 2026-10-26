// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/kmac.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/kmac.h"
#include "sw/device/lib/crypto/impl/cmvp.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/state.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/integrity.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('k', 'm', 'c')

/**
 * KMAC cleanup guard.
 */
OT_USED static void kmac_flush_guard(uint32_t *dummy) {
  (void)dummy;
  (void)kmac_fifo_flush();
}

/**
 * Sideload cleanup guard.
 */
OT_USED static void sideload_wipe_guard(hardened_bool_t *is_sideloaded) {
  if (*is_sideloaded == kHardenedBoolTrue) {
    (void)keymgr_sideload_clear_kmac();
  }
}

/**
 * Construct a KMAC driver key struct from a blinded key.
 *
 * If the key is hardware-backed, configures keymgr with diversification input
 * and generates the sideload key. If software-backed, remasks the key and
 * extracts the shares and integrity checksum.
 *
 * @param key The blinded input key.
 * @param key_len Key length in bytes.
 * @param[out] is_sideloaded Set to true if the key is sideloaded.
 * @param[out] kmac_key Destination KMAC driver key struct.
 * @return Result of the operation.
 */
static status_t kmac_key_construct(otcrypto_blinded_key_t *key, size_t key_len,
                                   hardened_bool_t *is_sideloaded,
                                   kmac_blinded_key_t *kmac_key) {
  kmac_key->share0 = NULL;
  kmac_key->share1 = NULL;
  kmac_key->hw_backed = key->config.hw_backed;
  kmac_key->len = key_len;

  if (key->config.hw_backed == kHardenedBoolTrue) {
    if (key_len != kKmacSideloadKeyLength / 8) {
      return OTCRYPTO_BAD_ARGS;
    }
    *is_sideloaded = kHardenedBoolTrue;

    // Configure keymgr with diversification input and then generate the
    // sideload key.
    keymgr_diversification_t diversification;
    // Diversification call also checks that `key->keyblob_length` is 8 words
    // long.
    HARDENED_TRY(keyblob_to_keymgr_diversification(key, &diversification));
    HARDENED_TRY(keymgr_generate_key_kmac(diversification));
  } else if (key->config.hw_backed == kHardenedBoolFalse) {
    // Check `key_len` matches `keyblob_length`.
    if (key->keyblob_length != 2 * key->config.key_length) {
      // COVERAGE (MISSING) We do not cover bad key_len inputs
      return OTCRYPTO_BAD_ARGS;
    }

    // Remask the key.
    HARDENED_TRY(keyblob_remask(key));
    HARDENED_TRY(keyblob_to_shares(key, &kmac_key->share0, &kmac_key->share1));
    // Set the checksum of the key.
    kmac_key->checksum = kmac_key_integrity_checksum(kmac_key);
  } else {
    return OTCRYPTO_BAD_ARGS;
  }

  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_kmac(
    otcrypto_blinded_key_t *key, const otcrypto_const_byte_buf_t *input_message,
    const otcrypto_const_byte_buf_t *customization_string,
    size_t required_output_len, otcrypto_word32_buf_t *tag) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_KMAC);
  OTCRYPTO_HEALTH_CHECK(kTestKmac256Bit);
  // TODO (#16410) Revisit/complete error checks

#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  // Check for null pointers.
  if (key == NULL || key->keyblob == NULL || tag == NULL || tag->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check for null input message with nonzero length.
  if (input_message == NULL ||
      (input_message->data == NULL && input_message->len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check for null customization string with nonzero length.
  if (customization_string == NULL ||
      (customization_string->data == NULL && customization_string->len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  hardened_bool_t is_sideloaded __attribute__((cleanup(sideload_wipe_guard))) =
      kHardenedBoolFalse;
  uint32_t hw_cleanup_guard __attribute__((cleanup(kmac_flush_guard))) = 1;
  barrier32(hw_cleanup_guard);

  // Ensure that tag buffer length and `required_output_len` match each other.
  if (required_output_len > SIZE_MAX - (sizeof(uint32_t) - 1)) {
    // COVERAGE (MISSING) Overflowing required_output_len is not covered.
    return OTCRYPTO_BAD_ARGS;
  }
  size_t required_output_words =
      (required_output_len + sizeof(uint32_t) - 1) / sizeof(uint32_t);

  // Per NIST SP 800-185, KMAC tag length must be at least 32 bits (4 bytes).
  if (tag->len != required_output_words || required_output_len < 4) {
    return OTCRYPTO_BAD_ARGS;
  }

  size_t key_len = key->config.key_length;

  // Check `key_len` is valid/supported by KMAC HWIP.
  HARDENED_TRY(kmac_key_length_check(key_len));

  // Check the integrity of the blinded key.
  if (launder32(otcrypto_integrity_blinded_key_check(key)) !=
      kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(otcrypto_integrity_blinded_key_check(key),
                    kHardenedBoolTrue);

  status_t (*kmac_fn)(kmac_blinded_key_t *, hardened_bool_t,
                      const otcrypto_const_byte_buf_t *, const unsigned char *,
                      size_t, uint32_t *, size_t) = NULL;
  otcrypto_key_mode_t key_mode_used = launder32(0);
  switch (launder32(key->config.key_mode)) {
    case kOtcryptoKeyModeKmac128:
      kmac_fn = kmac_kmac_128;
      key_mode_used = launder32(key_mode_used) | kOtcryptoKeyModeKmac128;
      break;
    case kOtcryptoKeyModeKmac256:
      kmac_fn = kmac_kmac_256;
      key_mode_used = launder32(key_mode_used) | kOtcryptoKeyModeKmac256;
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }
  // Check if we landed in the correct case statement. Use ORs for this to
  // avoid that multiple cases were executed.
  HARDENED_CHECK_EQ(launder32(key_mode_used), key->config.key_mode);

  kmac_blinded_key_t kmac_key;
  HARDENED_TRY(kmac_key_construct(key, key_len, &is_sideloaded, &kmac_key));

  // Preload the tag with randomness.
  HARDENED_TRY(hardened_memshred(tag->data, tag->len));

  if (launder32(key->config.security_level) == kOtcryptoKeySecurityLevelLow) {
    // No protection against FI.
    HARDENED_CHECK_EQ(key->config.security_level, kOtcryptoKeySecurityLevelLow);
    HARDENED_TRY(kmac_fn(&kmac_key, /*masked_digest=*/kHardenedBoolFalse,
                         input_message, customization_string->data,
                         customization_string->len, tag->data,
                         required_output_len));
  } else {
    // Call the KMAC core twice and compare both tags. This serves as a FI
    // countermeasure.
    HARDENED_CHECK_NE(key->config.security_level, kOtcryptoKeySecurityLevelLow);
    // First KMAC computation using the KMAC core.
    HARDENED_TRY(kmac_fn(&kmac_key, /*masked_digest=*/kHardenedBoolFalse,
                         input_message, customization_string->data,
                         customization_string->len, tag->data,
                         required_output_len));
    // Second KMAC computation using the KMAC core.
    uint32_t tag_redundant_data[required_output_words];
    HARDENED_TRY(hardened_memshred(tag_redundant_data, required_output_words));
    kmac_blinded_key_t kmac_key_redundant;
    HARDENED_TRY(
        kmac_key_construct(key, key_len, &is_sideloaded, &kmac_key_redundant));
    HARDENED_TRY(kmac_fn(&kmac_key_redundant,
                         /*masked_digest=*/kHardenedBoolFalse, input_message,
                         customization_string->data, customization_string->len,
                         tag_redundant_data, required_output_len));
    // Comparison of both tags.
    HARDENED_CHECK_EQ(
        hardened_memeq(&tag->data[0], &tag_redundant_data[0], tag->len),
        kHardenedBoolTrue);
  }

  // Verify the input buffer
  HARDENED_CHECK_EQ(kHardenedBoolTrue,
                    OTCRYPTO_CHECK_BUF(customization_string));

  return otcrypto_eval_exit(OTCRYPTO_OK);
}
