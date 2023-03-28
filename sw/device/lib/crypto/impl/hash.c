// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/hash.h"

#include <stdbool.h>

#include "sw/device/lib/crypto/drivers/hmac.h"
#include "sw/device/lib/crypto/drivers/kmac.h"
#include "sw/device/lib/crypto/impl/status.h"

/**
 * Return the digest size (in bytes) for given hashing mode.
 *
 * @param hash_mode Hashing mode (e.g. kHashModeSha256).
 * @param digest_len Result digest size in bytes.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
static crypto_status_t get_digest_size(hash_mode_t hash_mode,
                                       size_t *digest_len) {
  if (digest_len == NULL) {
    return kCryptoStatusBadArgs;
  }

  // Below `digest_len` is in bytes, therefore magic values are obtained
  // after division by 8.
  switch (hash_mode) {
    case kHashModeSha3_224:
      *digest_len = 224 / 8;
      break;
    case kHashModeSha256:
      OT_FALLTHROUGH_INTENDED;
    case kHashModeSha3_256:
      *digest_len = 256 / 8;
      break;
    case kHashModeSha384:
      OT_FALLTHROUGH_INTENDED;
    case kHashModeSha3_384:
      *digest_len = 384 / 8;
      break;
    case kHashModeSha512:
      OT_FALLTHROUGH_INTENDED;
    case kHashModeSha3_512:
      *digest_len = 512 / 8;
      break;
    default:
      return kCryptoStatusBadArgs;
  }
  return kCryptoStatusOK;
}

/**
 * Compute SHA256 using the HMAC hardware block.
 *
 * @param message Message to hash.
 * @param[out] digest Output digest.
 */
OT_WARN_UNUSED_RESULT
static status_t sha256(crypto_const_uint8_buf_t message,
                       crypto_uint8_buf_t *digest) {
  HARDENED_CHECK_EQ(digest->len, kHmacDigestNumBytes);

  // Initialize the hardware.
  hmac_sha256_init();

  // Pass the message and check the length.
  hmac_update(message.data, message.len);

  // Retrieve the digest and copy it to the destination buffer.
  hmac_digest_t hmac_digest;
  hmac_final(&hmac_digest);
  memcpy(digest->data, hmac_digest.digest, kHmacDigestNumBytes);

  return OTCRYPTO_OK;
}

crypto_status_t otcrypto_hash(crypto_const_uint8_buf_t input_message,
                              hash_mode_t hash_mode,
                              crypto_uint8_buf_t *digest) {
  if (input_message.data == NULL && input_message.len != 0) {
    return kCryptoStatusBadArgs;
  }

  if (digest == NULL || digest->data == NULL) {
    return kCryptoStatusBadArgs;
  }

  // Check `digest->len` is consistent with `hash_mode`
  size_t expected_digest_len;
  crypto_status_t err_status = get_digest_size(hash_mode, &expected_digest_len);
  if (err_status != kCryptoStatusOK) {
    return err_status;
  } else if (expected_digest_len != digest->len) {
    return kCryptoStatusBadArgs;
  }

  kmac_error_t err = kKmacOk;
  switch (hash_mode) {
    case kHashModeSha3_224:
      err = kmac_sha3_224(input_message, digest);
      break;
    case kHashModeSha3_256:
      err = kmac_sha3_256(input_message, digest);
      break;
    case kHashModeSha3_384:
      err = kmac_sha3_384(input_message, digest);
      break;
    case kHashModeSha3_512:
      err = kmac_sha3_512(input_message, digest);
      break;
    case kHashModeSha256:
      // Call the HMAC block driver in SHA-256 mode.
      OTCRYPTO_TRY_INTERPRET(sha256(input_message, digest));
      break;
    default:
      // TODO: (#16410) Connect SHA2-{384,512} implementations
      return kCryptoStatusBadArgs;
  }

  // TODO: (#14549, #16410) Revisit KMAC error flow
  // Need to map KMAC driver error enum to cryptolib error enum
  if (err != kKmacOk) {
    return kCryptoStatusBadArgs;
  }

  return kCryptoStatusOK;
}

crypto_status_t otcrypto_xof(crypto_const_uint8_buf_t input_message,
                             xof_mode_t xof_mode,
                             crypto_const_uint8_buf_t function_name_string,
                             crypto_const_uint8_buf_t customization_string,
                             size_t required_output_len,
                             crypto_uint8_buf_t *digest) {
  // TODO: (#16410) Add error checks
  if (required_output_len != digest->len) {
    return kCryptoStatusBadArgs;
  }

  // According to NIST SP 800-185 Section 3.2, cSHAKE call should use SHAKE, if
  // both `customization_string` and `function_name_string` are empty string
  if (customization_string.len == 0 && function_name_string.len == 0) {
    if (xof_mode == kXofModeSha3Cshake128) {
      xof_mode = kXofModeSha3Shake128;
    } else if (xof_mode == kXofModeSha3Cshake256) {
      xof_mode = kXofModeSha3Shake256;
    }
  }

  kmac_error_t err;
  switch (xof_mode) {
    case kXofModeSha3Shake128:
      err = kmac_shake_128(input_message, digest);
      break;
    case kXofModeSha3Shake256:
      err = kmac_shake_256(input_message, digest);
      break;
    case kXofModeSha3Cshake128:
      err = kmac_cshake_128(input_message, function_name_string,
                            customization_string, digest);
      break;
    case kXofModeSha3Cshake256:
      err = kmac_cshake_256(input_message, function_name_string,
                            customization_string, digest);
      break;
    default:
      return kCryptoStatusBadArgs;
  }

  // TODO: (#14549, #16410) Revisit KMAC error flow
  if (err != kKmacOk) {
    return kCryptoStatusBadArgs;
  }

  return kCryptoStatusOK;
}
