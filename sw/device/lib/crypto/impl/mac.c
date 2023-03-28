// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/mac.h"

#include <stdbool.h>

#include "sw/device/lib/crypto/drivers/hmac.h"
#include "sw/device/lib/crypto/drivers/kmac.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/status.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('m', 'a', 'c')

/**
 * Call the hardware HMAC-SHA256 driver.
 *
 * Note: the hardware implementation is unhardened against side-channel and
 * fault attacks.
 *
 * @param key HMAC key.
 * @param message Input message.
 * @param[out] tag Output tag.
 */
OT_WARN_UNUSED_RESULT
static status_t hmac_sha256(const crypto_blinded_key_t *key,
                            crypto_const_uint8_buf_t message,
                            crypto_uint8_buf_t *tag) {
  // Should never be called if the following checks fail; this indicates a
  // possible fault attack.
  HARDENED_CHECK_EQ(key->config.key_mode, kKeyModeHmacSha256);
  HARDENED_CHECK_EQ(tag->len, kHmacDigestNumBytes);

  // Get the individual key shares.
  uint32_t *share0;
  uint32_t *share1;
  HARDENED_TRY(keyblob_to_shares(key, &share0, &share1));

  // Convert the key to the HMAC-specific struct.
  // NOTE: this unmasks the key, because the HMAC hardware is unhardened.
  // TODO: randomize the iteration order of this loop.
  hmac_key_t hmac_key;
  for (size_t i = 0; i < kHmacKeyNumWords; i++) {
    hmac_key.key[i] = share0[i] ^ share1[i];
  }

  // Initialize the hardware.
  hmac_hmac_init(&hmac_key);

  // Pass the message.
  hmac_update(message.data, message.len);

  // Retrieve the digest and copy it to the destination buffer.
  hmac_digest_t hmac_digest;
  hmac_final(&hmac_digest);
  memcpy(tag->data, hmac_digest.digest, kHmacDigestNumBytes);

  return OTCRYPTO_OK;
}

OT_WARN_UNUSED_RESULT
crypto_status_t otcrypto_mac(const crypto_blinded_key_t *key,
                             crypto_const_uint8_buf_t input_message,
                             mac_mode_t mac_mode,
                             crypto_const_uint8_buf_t customization_string,
                             size_t required_output_len,
                             crypto_uint8_buf_t *tag) {
  // TODO (#16410) Revisit/complete error checks

  // Check for null pointers.
  if (key == NULL || key->keyblob == NULL || tag == NULL || tag->data == NULL) {
    return kCryptoStatusBadArgs;
  }

  // Check for null input message with nonzero length.
  if (input_message.data == NULL && input_message.len != 0) {
    return kCryptoStatusBadArgs;
  }

  // Check for null customization string with nonzero length.
  if (customization_string.data == NULL && customization_string.len != 0) {
    return kCryptoStatusBadArgs;
  }

  size_t key_len = keyblob_share_num_words(key->config) * sizeof(uint32_t);

  // Check `key_len` is valid/supported by KMAC HWIP.
  OTCRYPTO_TRY_INTERPRET(kmac_key_length_check(key_len));

  // Check the integrity of the blinded key.
  if (integrity_blinded_key_check(key) != kHardenedBoolTrue) {
    return kCryptoStatusBadArgs;
  }

  // TODO (#16410, #15590): Add sideload support.
  if (key->config.hw_backed == kHardenedBoolTrue) {
    return kCryptoStatusBadArgs;
  }

  kmac_blinded_key_t kmac_key;
  OTCRYPTO_TRY_INTERPRET(
      keyblob_to_shares(key, &kmac_key.share0, &kmac_key.share1));
  kmac_key.len = key_len;

  switch (mac_mode) {
    case kMacModeKmac128:
      // Check `key_mode` matches `mac_mode`
      if (key->config.key_mode != kKeyModeKmac128) {
        return kCryptoStatusBadArgs;
      }
      OTCRYPTO_TRY_INTERPRET(
          kmac_kmac_128(&kmac_key, input_message, customization_string, tag));
      break;
    case kMacModeKmac256:
      // Check `key_mode` matches `mac_mode`
      if (key->config.key_mode != kKeyModeKmac256) {
        return kCryptoStatusBadArgs;
      }

      OTCRYPTO_TRY_INTERPRET(
          kmac_kmac_256(&kmac_key, input_message, customization_string, tag));
      break;
    case kMacModeHmacSha256:
      // Check `key_mode` matches `mac_mode`
      if (key->config.key_mode != kKeyModeHmacSha256) {
        return kCryptoStatusBadArgs;
      }
      // Check tag length.
      if (tag->len != kHmacDigestNumBytes) {
        return kCryptoStatusBadArgs;
      }
      // Call hardware HMAC driver.
      OTCRYPTO_TRY_INTERPRET(hmac_sha256(key, input_message, tag));
      break;
    default:
      return kCryptoStatusBadArgs;
  }

  return kCryptoStatusOK;
}
