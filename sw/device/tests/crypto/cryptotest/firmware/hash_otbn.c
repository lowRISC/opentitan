// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/impl/sha2/sha256.h"
#include "sw/device/lib/crypto/impl/sha2/sha384.h"
#include "sw/device/lib/crypto/impl/sha2/sha512.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/integrity.h"
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
  otcrypto_const_byte_buf_t input_message = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, msg_buf, uj_message.message_len);
  uint8_t customization_string_buf[uj_message.customization_string_len];
  memcpy(customization_string_buf, uj_message.customization_string,
         uj_message.customization_string_len);
  otcrypto_const_byte_buf_t customization_string =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, customization_string_buf,
                        uj_message.customization_string_len);
  // If we are using cSHAKE, the empty function name tells cryptolib not to
  // apply any function on top of cSHAKE.
  otcrypto_const_byte_buf_t cshake_function_name =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 0);

  // Handle to correct oneshot hash API for the provided algorithm
  otcrypto_status_t (*hash_oneshot)(const otcrypto_const_byte_buf_t *,
                                    otcrypto_hash_digest_t *);

  // Digest length in 32-bit words
  size_t digest_len;
  uint8_t test_stepwise = false;
  switch (uj_algorithm) {
    case kCryptotestHashAlgorithmSha256:
      digest_len = 256 / 32;
      test_stepwise = true;
      break;
    case kCryptotestHashAlgorithmSha384:
      digest_len = 384 / 32;
      test_stepwise = true;
      break;
    case kCryptotestHashAlgorithmSha512:
      digest_len = 512 / 32;
      test_stepwise = true;
      break;
    case kCryptotestHashAlgorithmSha3_224:
      digest_len = 224 / 32;
      hash_oneshot = otcrypto_sha3_224;
      break;
    case kCryptotestHashAlgorithmSha3_256:
      digest_len = 256 / 32;
      hash_oneshot = otcrypto_sha3_256;
      break;
    case kCryptotestHashAlgorithmSha3_384:
      digest_len = 384 / 32;
      hash_oneshot = otcrypto_sha3_384;
      break;
    case kCryptotestHashAlgorithmSha3_512:
      digest_len = 512 / 32;
      hash_oneshot = otcrypto_sha3_512;
      break;
    case kCryptotestHashAlgorithmShake128:
      digest_len = ceil_div(uj_shake_digest_length.length, sizeof(uint32_t));
      hash_oneshot = otcrypto_shake128;
      break;
    case kCryptotestHashAlgorithmShake256:
      digest_len = ceil_div(uj_shake_digest_length.length, sizeof(uint32_t));
      hash_oneshot = otcrypto_shake256;
      break;
    case kCryptotestHashAlgorithmCshake128:
      digest_len = ceil_div(uj_shake_digest_length.length, sizeof(uint32_t));
      break;
    case kCryptotestHashAlgorithmCshake256:
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
    case kCryptotestHashAlgorithmSha256:
      status = sha256(input_message.data, input_message.len, digest_buf);
      break;
    case kCryptotestHashAlgorithmSha384:
      status = sha384(input_message.data, input_message.len, digest_buf);
      break;
    case kCryptotestHashAlgorithmSha512:
      status = sha512(input_message.data, input_message.len, digest_buf);
      break;
    case kCryptotestHashAlgorithmCshake128:
      status = otcrypto_cshake128(&input_message, &cshake_function_name,
                                  &customization_string, &digest);
      break;
    case kCryptotestHashAlgorithmCshake256:
      status = otcrypto_cshake256(&input_message, &cshake_function_name,
                                  &customization_string, &digest);
      break;
    default:
      status = hash_oneshot(&input_message, &digest);
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
    size_t half_len = uj_message.message_len / 2;
    size_t rem_len = ceil_div(uj_message.message_len, 2);
    switch (uj_algorithm) {
      case kCryptotestHashAlgorithmSha256: {
        sha256_state_t state;
        status = sha256_init(&state);
        if (status.value != kOtcryptoStatusValueOk) {
          return INTERNAL(status.value);
        }
        status = sha256_update(&state, msg_buf, half_len);
        if (status.value != kOtcryptoStatusValueOk) {
          return INTERNAL(status.value);
        }
        status = sha256_update(&state, &msg_buf[half_len], rem_len);
        if (status.value != kOtcryptoStatusValueOk) {
          return INTERNAL(status.value);
        }
        status = sha256_final(&state, digest_buf);
        if (status.value != kOtcryptoStatusValueOk) {
          return INTERNAL(status.value);
        }
        break;
      }
      case kCryptotestHashAlgorithmSha384: {
        sha384_state_t state;
        status = sha384_init(&state);
        if (status.value != kOtcryptoStatusValueOk) {
          return INTERNAL(status.value);
        }
        status = sha384_update(&state, msg_buf, half_len);
        if (status.value != kOtcryptoStatusValueOk) {
          return INTERNAL(status.value);
        }
        status = sha384_update(&state, &msg_buf[half_len], rem_len);
        if (status.value != kOtcryptoStatusValueOk) {
          return INTERNAL(status.value);
        }
        status = sha384_final(&state, digest_buf);
        if (status.value != kOtcryptoStatusValueOk) {
          return INTERNAL(status.value);
        }
        break;
      }
      case kCryptotestHashAlgorithmSha512: {
        sha512_state_t state;
        status = sha512_init(&state);
        if (status.value != kOtcryptoStatusValueOk) {
          return INTERNAL(status.value);
        }
        status = sha512_update(&state, msg_buf, half_len);
        if (status.value != kOtcryptoStatusValueOk) {
          return INTERNAL(status.value);
        }
        status = sha512_update(&state, &msg_buf[half_len], rem_len);
        if (status.value != kOtcryptoStatusValueOk) {
          return INTERNAL(status.value);
        }
        status = sha512_final(&state, digest_buf);
        if (status.value != kOtcryptoStatusValueOk) {
          return INTERNAL(status.value);
        }
        break;
      }
      default:
        break;
    }
    // Copy stepwise result to uJSON type
    memcpy(uj_output.stepwise_digest, digest_buf,
           digest_len * sizeof(uint32_t));
  }
  // Send digest to host via UART
  RESP_OK(ujson_serialize_cryptotest_hash_output_t, uj, &uj_output);
  return OK_STATUS(0);
}
