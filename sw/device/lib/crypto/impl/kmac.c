// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/kmac.h"

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/drivers/kmac.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/status.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('k', 'm', 'c')

otcrypto_status_t otcrypto_kmac(otcrypto_blinded_key_t *key,
                                otcrypto_const_byte_buf_t input_message,
                                otcrypto_const_byte_buf_t customization_string,
                                size_t required_output_len,
                                otcrypto_word32_buf_t tag) {
  // TODO (#16410) Revisit/complete error checks

  // Check for null pointers.
  if (key == NULL || key->keyblob == NULL || tag.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check for null input message with nonzero length.
  if (input_message.data == NULL && input_message.len != 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check for null customization string with nonzero length.
  if (customization_string.data == NULL && customization_string.len != 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Ensure that tag buffer length and `required_output_len` match each other.
  if (required_output_len != tag.len * sizeof(uint32_t) ||
      required_output_len == 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Ensure the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  size_t key_len = keyblob_share_num_words(key->config) * sizeof(uint32_t);

  // Check `key_len` is valid/supported by KMAC HWIP.
  HARDENED_TRY(kmac_key_length_check(key_len));

  // Check the integrity of the blinded key.
  if (launder32(integrity_blinded_key_check(key)) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(integrity_blinded_key_check(key), kHardenedBoolTrue);

  kmac_blinded_key_t kmac_key = {
      .share0 = NULL,
      .share1 = NULL,
      .hw_backed = key->config.hw_backed,
      .len = key_len,
  };

  if (key->config.hw_backed == kHardenedBoolTrue) {
    if (key_len != kKmacSideloadKeyLength / 8) {
      return OTCRYPTO_BAD_ARGS;
    }
    // Configure keymgr with diversification input and then generate the
    // sideload key.
    keymgr_diversification_t diversification;
    // Diversification call also checks that `key->keyblob_length` is 8 words
    // long.
    HARDENED_TRY(keyblob_to_keymgr_diversification(key, &diversification));
    HARDENED_TRY(keymgr_generate_key_kmac(diversification));
  } else if (key->config.hw_backed == kHardenedBoolFalse) {
    // Remask the key.
    HARDENED_TRY(keyblob_remask(key));

    // Check `key_len` matches `keyblob_length`.
    if (key->keyblob_length != 2 * key->config.key_length) {
      return OTCRYPTO_BAD_ARGS;
    }
    HARDENED_TRY(keyblob_to_shares(key, &kmac_key.share0, &kmac_key.share1));
  } else {
    return OTCRYPTO_BAD_ARGS;
  }

  switch (key->config.key_mode) {
    case kOtcryptoKeyModeKmac128:
      HARDENED_TRY(kmac_kmac_128(
          &kmac_key, /*masked_digest=*/kHardenedBoolFalse, input_message.data,
          input_message.len, customization_string.data,
          customization_string.len, tag.data, tag.len));
      break;
    case kOtcryptoKeyModeKmac256:
      HARDENED_TRY(kmac_kmac_256(
          &kmac_key, /*masked_digest=*/kHardenedBoolFalse, input_message.data,
          input_message.len, customization_string.data,
          customization_string.len, tag.data, tag.len));
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  if (key->config.hw_backed == kHardenedBoolTrue) {
    HARDENED_TRY(keymgr_sideload_clear_kmac());
  } else if (key->config.hw_backed != kHardenedBoolFalse) {
    return OTCRYPTO_BAD_ARGS;
  }

  return OTCRYPTO_OK;
}
