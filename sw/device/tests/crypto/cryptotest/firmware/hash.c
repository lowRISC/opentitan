// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/sha2.h"
#include "sw/device/lib/crypto/include/sha3.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/crypto/cryptotest/json/hash_commands.h"

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
  uint8_t customization_string_buf[uj_message.customization_string_len];
  memcpy(customization_string_buf, uj_message.customization_string,
         uj_message.customization_string_len);
  otcrypto_const_byte_buf_t customization_string = {
      .len = uj_message.customization_string_len,
      .data = customization_string_buf,
  };
  // If we are using cSHAKE, the empty function name tells cryptolib not to
  // apply any function on top of cSHAKE.
  otcrypto_const_byte_buf_t cshake_function_name = {
      .len = 0,
  };

  // Handle to correct oneshot hash API for the provided algorithm
  otcrypto_status_t (*hash_oneshot)(otcrypto_const_byte_buf_t,
                                    otcrypto_hash_digest_t *);

  // Digest length in 32-bit words
  size_t digest_len;
  uint8_t test_stepwise = false;
  otcrypto_hash_mode_t mode;
  switch (uj_algorithm) {
    case kCryptotestHashAlgorithmSha256:
      mode = kOtcryptoHashModeSha256;
      digest_len = 256 / 32;
      hash_oneshot = otcrypto_sha2_256;
      test_stepwise = true;
      break;
    case kCryptotestHashAlgorithmSha384:
      mode = kOtcryptoHashModeSha384;
      digest_len = 384 / 32;
      hash_oneshot = otcrypto_sha2_384;
      test_stepwise = true;
      break;
    case kCryptotestHashAlgorithmSha512:
      mode = kOtcryptoHashModeSha512;
      digest_len = 512 / 32;
      hash_oneshot = otcrypto_sha2_512;
      test_stepwise = true;
      break;
    case kCryptotestHashAlgorithmSha3_224:
      mode = kOtcryptoHashModeSha3_224;
      digest_len = 224 / 32;
      hash_oneshot = otcrypto_sha3_224;
      break;
    case kCryptotestHashAlgorithmSha3_256:
      mode = kOtcryptoHashModeSha3_256;
      digest_len = 256 / 32;
      hash_oneshot = otcrypto_sha3_256;
      break;
    case kCryptotestHashAlgorithmSha3_384:
      mode = kOtcryptoHashModeSha3_384;
      digest_len = 384 / 32;
      hash_oneshot = otcrypto_sha3_384;
      break;
    case kCryptotestHashAlgorithmSha3_512:
      mode = kOtcryptoHashModeSha3_512;
      digest_len = 512 / 32;
      hash_oneshot = otcrypto_sha3_512;
      break;
    case kCryptotestHashAlgorithmShake128:
      mode = kOtcryptoHashXofModeShake128;
      digest_len = ceil_div(uj_shake_digest_length.length, sizeof(uint32_t));
      hash_oneshot = otcrypto_shake128;
      break;
    case kCryptotestHashAlgorithmShake256:
      mode = kOtcryptoHashXofModeShake256;
      digest_len = ceil_div(uj_shake_digest_length.length, sizeof(uint32_t));
      hash_oneshot = otcrypto_shake256;
      break;
    case kCryptotestHashAlgorithmCshake128:
      mode = kOtcryptoHashXofModeCshake128;
      digest_len = ceil_div(uj_shake_digest_length.length, sizeof(uint32_t));
      break;
    case kCryptotestHashAlgorithmCshake256:
      mode = kOtcryptoHashXofModeCshake256;
      digest_len = ceil_div(uj_shake_digest_length.length, sizeof(uint32_t));
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
      .len = digest_len,
  };
  otcrypto_status_t status;
  // Test oneshot API
  switch (uj_algorithm) {
    case kCryptotestHashAlgorithmCshake128:
      status = otcrypto_cshake128(input_message, cshake_function_name,
                                  customization_string, &digest);
      break;
    case kCryptotestHashAlgorithmCshake256:
      status = otcrypto_cshake256(input_message, cshake_function_name,
                                  customization_string, &digest);
      break;
    default:
      status = hash_oneshot(input_message, &digest);
  }
  if (status.value != kOtcryptoStatusValueOk) {
    LOG_ERROR("Bad status value: 0x%x", status.value);
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
    otcrypto_sha2_context_t ctx;
    status = otcrypto_sha2_init(mode, &ctx);
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
    status = otcrypto_sha2_update(&ctx, input_message_share1);
    if (status.value != kOtcryptoStatusValueOk) {
      return INTERNAL(status.value);
    }
    status = otcrypto_sha2_update(&ctx, input_message_share2);
    if (status.value != kOtcryptoStatusValueOk) {
      return INTERNAL(status.value);
    }
    status = otcrypto_sha2_final(&ctx, &digest);
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
