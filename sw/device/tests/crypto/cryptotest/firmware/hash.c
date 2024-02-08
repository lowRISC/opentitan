// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/hash.h"

#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/sha2/sha256.h"
#include "sw/device/lib/crypto/impl/sha2/sha512.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/crypto/cryptotest/json/hash_commands.h"

enum {
  kSha3_256DigestWords = kSha256DigestWords,
  kSha3_384DigestWords = kSha384DigestWords,
  kSha3_512DigestWords = kSha512DigestWords,
};

status_t handle_hash(ujson_t *uj) {
  // Declare test arguments
  cryptotest_hash_algorithm_t uj_algorithm;
  cryptotest_hash_shake_digest_length_t uj_shake_digest_length;
  cryptotest_hash_message_t uj_message;
  // Deserialize test arguments from UART
  TRY(ujson_deserialize_cryptotest_hash_algorithm_t(uj, &uj_algorithm));
  TRY(ujson_deserialize_cryptotest_hash_shake_digest_length_t(
      uj, &uj_shake_digest_length));
  TRY(ujson_deserialize_cryptotest_hash_message_t(uj, &uj_message));

  // Create input message
  uint8_t msg_buf[uj_message.message_len];
  memcpy(msg_buf, uj_message.message, uj_message.message_len);
  otcrypto_const_byte_buf_t input_message = {
      .len = uj_message.message_len,
      .data = msg_buf,
  };

  // Handle to correct oneshot hash API for the provided algorithm
  otcrypto_status_t (*hash_oneshot)(otcrypto_const_byte_buf_t,
                                    otcrypto_hash_digest_t);

  // Digest length in 32-bit words
  size_t digest_len;
  uint8_t test_stepwise = false;
  otcrypto_hash_mode_t mode;
  switch (uj_algorithm) {
    case kCryptotestHashAlgorithmSha256:
      mode = kOtcryptoHashModeSha256;
      digest_len = kSha256DigestWords;
      hash_oneshot = otcrypto_hash;
      test_stepwise = true;
      break;
    case kCryptotestHashAlgorithmSha384:
      mode = kOtcryptoHashModeSha384;
      digest_len = kSha384DigestWords;
      hash_oneshot = otcrypto_hash;
      test_stepwise = true;
      break;
    case kCryptotestHashAlgorithmSha512:
      mode = kOtcryptoHashModeSha512;
      digest_len = kSha512DigestWords;
      hash_oneshot = otcrypto_hash;
      test_stepwise = true;
      break;
    case kCryptotestHashAlgorithmSha3_256:
      mode = kOtcryptoHashModeSha3_256;
      digest_len = kSha3_256DigestWords;
      hash_oneshot = otcrypto_hash;
      break;
    case kCryptotestHashAlgorithmSha3_384:
      mode = kOtcryptoHashModeSha3_384;
      digest_len = kSha3_384DigestWords;
      hash_oneshot = otcrypto_hash;
      break;
    case kCryptotestHashAlgorithmSha3_512:
      mode = kOtcryptoHashModeSha3_512;
      digest_len = kSha3_512DigestWords;
      hash_oneshot = otcrypto_hash;
      break;
    case kCryptotestHashAlgorithmShake128:
      mode = kOtcryptoHashXofModeShake128;
      digest_len = ceil_div(uj_shake_digest_length.length, sizeof(uint32_t));
      hash_oneshot = otcrypto_xof_shake;
      break;
    case kCryptotestHashAlgorithmShake256:
      mode = kOtcryptoHashXofModeShake256;
      digest_len = ceil_div(uj_shake_digest_length.length, sizeof(uint32_t));
      hash_oneshot = otcrypto_xof_shake;
      break;
    default:
      LOG_ERROR("Unsupported hash algorithm: %d", uj_algorithm);
      return INVALID_ARGUMENT();
  }

  // Create digest skeleton
  uint32_t digest_buf[digest_len];
  memset(digest_buf, 0, digest_len * sizeof(uint32_t));
  otcrypto_hash_digest_t digest = {
      .data = digest_buf,
      .mode = mode,
      .len = digest_len,
  };

  // Test oneshot API
  otcrypto_status_t status = hash_oneshot(input_message, digest);
  if (status.value != kOtcryptoStatusValueOk) {
    return INTERNAL(status.value);
  }
  cryptotest_hash_output_t uj_output;
  uj_output.digest_len = digest_len * sizeof(uint32_t);
  // Copy oneshot digest to uJSON type
  memcpy(uj_output.oneshot_digest, digest_buf, digest_len * sizeof(uint32_t));
  // Zero out digest_buf to mitigate chance of a false positive in the
  // stepwise test
  memset(digest_buf, 0, digest_len * sizeof(uint32_t));
  // Test the stepwise API for algorithms that support it
  if (test_stepwise) {
    otcrypto_hash_context_t ctx;
    status = otcrypto_hash_init(&ctx, mode);
    if (status.value != kOtcryptoStatusValueOk) {
      return INTERNAL(status.value);
    }
    // Split up input mesasge into 2 shares for better coverage of stepwise
    // hashing
    otcrypto_const_byte_buf_t input_message_share1 = {
        .len = uj_message.message_len / 2,
        .data = msg_buf,
    };
    otcrypto_const_byte_buf_t input_message_share2 = {
        .len = ceil_div(uj_message.message_len, 2),
        .data = &msg_buf[uj_message.message_len / 2],
    };
    status = otcrypto_hash_update(&ctx, input_message_share1);
    if (status.value != kOtcryptoStatusValueOk) {
      return INTERNAL(status.value);
    }
    status = otcrypto_hash_update(&ctx, input_message_share2);
    if (status.value != kOtcryptoStatusValueOk) {
      return INTERNAL(status.value);
    }
    status = otcrypto_hash_final(&ctx, digest);
    if (status.value != kOtcryptoStatusValueOk) {
      return INTERNAL(status.value);
    }
    // Copy stepwise result to uJSON type
    memcpy(uj_output.stepwise_digest, digest_buf,
           digest_len * sizeof(uint32_t));
  }
  // Send digest to host via UART
  RESP_OK(ujson_serialize_cryptotest_hash_output_t, uj, &uj_output);
  return OK_STATUS(0);
}
