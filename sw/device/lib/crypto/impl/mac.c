// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/mac.h"

#include <stdbool.h>

#include "sw/device/lib/crypto/drivers/kmac.h"

OT_WARN_UNUSED_RESULT
crypto_status_t otcrypto_mac(const crypto_blinded_key_t *key,
                             crypto_const_uint8_buf_t input_message,
                             mac_mode_t mac_mode,
                             crypto_const_uint8_buf_t customization_string,
                             size_t required_output_len,
                             crypto_uint8_buf_t *tag) {
  // TODO (#16410) Revisit/complete error checks

  kmac_error_t err;
  size_t key_len = key->config.key_length;

  // TODO (#16410, #15590): Add sideload support.
  if (key->config.hw_backed == kHardenedBoolTrue) {
    return kCryptoStatusBadArgs;
  } else if (key->keyblob_length != 2 * key_len) {
    return kCryptoStatusBadArgs;
  }

  // Check `key_len` is valid/supported by KMAC HWIP.
  if (!kmac_is_valid_key_len(key_len)) {
    return kCryptoStatusBadArgs;
  }

  kmac_blinded_key_t kmac_key = {
      .share0 = key->keyblob,
      .share1 = key->keyblob + key_len / 4,
      .len = key_len,
  };

  switch (mac_mode) {
    case kMacModeKmac128:
      // Check `key_mode` matches `mac_mode`
      if (key->config.key_mode != kKeyModeKmac128) {
        return kCryptoStatusBadArgs;
      }

      err = kmac_kmac_128(&kmac_key, input_message, customization_string, tag);
      break;
    case kMacModeKmac256:
      // Check `key_mode` matches `mac_mode`
      if (key->config.key_mode != kKeyModeKmac256) {
        return kCryptoStatusBadArgs;
      }

      err = kmac_kmac_256(&kmac_key, input_message, customization_string, tag);
      break;
    case kMacModeHmacSha256:
      // HMAC SHA-256 not implemented yet.
      OT_FALLTHROUGH_INTENDED;
    default:
      return kCryptoStatusBadArgs;
  }

  // TODO (#16410) Error checks
  if (err != kKmacOk) {
    return kCryptoStatusBadArgs;
  }

  return kCryptoStatusOK;
}
