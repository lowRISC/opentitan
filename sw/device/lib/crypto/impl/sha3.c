// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/sha3.h"

#include <stdbool.h>

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/kmac.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/config.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('s', 'h', '3')

otcrypto_status_t otcrypto_sha3_224(const otcrypto_const_byte_buf_t *message,
                                    otcrypto_hash_digest_t *digest) {
  if (digest == NULL || digest->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (message == NULL || (message->data == NULL && message->len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (launder32(digest->len) != kKmacSha3224DigestWords) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(digest->len, kKmacSha3224DigestWords);
  digest->mode = kOtcryptoHashModeSha3_224;
  return otcrypto_eval_exit(kmac_sha3_224(message, digest->data));
}

otcrypto_status_t otcrypto_sha3_256(const otcrypto_const_byte_buf_t *message,
                                    otcrypto_hash_digest_t *digest) {
  if (digest == NULL || digest->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (message == NULL || (message->data == NULL && message->len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (launder32(digest->len) != kKmacSha3256DigestWords) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(digest->len, kKmacSha3256DigestWords);
  digest->mode = kOtcryptoHashModeSha3_256;
  return otcrypto_eval_exit(kmac_sha3_256(message, digest->data));
}

otcrypto_status_t otcrypto_sha3_384(const otcrypto_const_byte_buf_t *message,
                                    otcrypto_hash_digest_t *digest) {
  if (digest == NULL || digest->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (message == NULL || (message->data == NULL && message->len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (launder32(digest->len) != kKmacSha3384DigestWords) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(digest->len, kKmacSha3384DigestWords);
  digest->mode = kOtcryptoHashModeSha3_384;
  return otcrypto_eval_exit(kmac_sha3_384(message, digest->data));
}

otcrypto_status_t otcrypto_sha3_512(const otcrypto_const_byte_buf_t *message,
                                    otcrypto_hash_digest_t *digest) {
  if (digest == NULL || digest->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (message == NULL || (message->data == NULL && message->len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (launder32(digest->len) != kKmacSha3512DigestWords) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(digest->len, kKmacSha3512DigestWords);
  digest->mode = kOtcryptoHashModeSha3_512;
  return otcrypto_eval_exit(kmac_sha3_512(message, digest->data));
}

otcrypto_status_t otcrypto_shake128(const otcrypto_const_byte_buf_t *message,
                                    otcrypto_hash_digest_t *digest) {
  if (digest == NULL || digest->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (message == NULL || (message->data == NULL && message->len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }
  digest->mode = kOtcryptoHashXofModeShake128;
  return otcrypto_eval_exit(kmac_shake_128(message, digest->data, digest->len));
}

otcrypto_status_t otcrypto_shake256(const otcrypto_const_byte_buf_t *message,
                                    otcrypto_hash_digest_t *digest) {
  if (digest == NULL || digest->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (message == NULL || (message->data == NULL && message->len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }
  digest->mode = kOtcryptoHashXofModeShake256;
  return otcrypto_eval_exit(kmac_shake_256(message, digest->data, digest->len));
}

otcrypto_status_t otcrypto_cshake128(
    const otcrypto_const_byte_buf_t *message,
    const otcrypto_const_byte_buf_t *function_name_string,
    const otcrypto_const_byte_buf_t *customization_string,
    otcrypto_hash_digest_t *digest) {
  if (digest == NULL || digest->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (message == NULL || (message->data == NULL && message->len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (function_name_string == NULL ||
      (function_name_string->data == NULL && function_name_string->len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (customization_string == NULL ||
      (customization_string->data == NULL && customization_string->len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }
  digest->mode = kOtcryptoHashXofModeCshake128;
  return otcrypto_eval_exit(
      kmac_cshake_128(message, function_name_string->data,
                      function_name_string->len, customization_string->data,
                      customization_string->len, digest->data, digest->len));
}

otcrypto_status_t otcrypto_cshake256(
    const otcrypto_const_byte_buf_t *message,
    const otcrypto_const_byte_buf_t *function_name_string,
    const otcrypto_const_byte_buf_t *customization_string,
    otcrypto_hash_digest_t *digest) {
  if (digest == NULL || digest->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (message == NULL || (message->data == NULL && message->len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (function_name_string == NULL ||
      (function_name_string->data == NULL && function_name_string->len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (customization_string == NULL ||
      (customization_string->data == NULL && customization_string->len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }
  digest->mode = kOtcryptoHashXofModeCshake256;
  return otcrypto_eval_exit(
      kmac_cshake_256(message, function_name_string->data,
                      function_name_string->len, customization_string->data,
                      customization_string->len, digest->data, digest->len));
}
