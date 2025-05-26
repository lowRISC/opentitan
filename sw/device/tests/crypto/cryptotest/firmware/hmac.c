// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/hmac.h"

#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/key_transport.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/crypto/cryptotest/json/hmac_commands.h"

const unsigned int kOtcryptoHmacTagBytesSha256 = 32;
const unsigned int kOtcryptoHmacTagBytesSha384 = 48;
const unsigned int kOtcryptoHmacTagBytesSha512 = 64;

const int MaxTagBytes = kOtcryptoHmacTagBytesSha512;
const int MaxTagWords = MaxTagBytes / sizeof(uint32_t);

// Random value for masking, as large as the longest test key. This value
// should not affect the result.
static const uint32_t kTestMask[48] = {
    0xBA81767F, 0xA913C751, 0x34209992, 0x5F66021B, 0x775F4577, 0x7C02E1CE,
    0xB4A8B698, 0x1986B902, 0x7251045B, 0x3C827C6F, 0x00909D12, 0x81ABC8F9,
    0x62F2FCB6, 0x15B63124, 0x66F60052, 0xAD637669, 0x522779CF, 0x07E9FBA8,
    0x1258E541, 0x860719EF, 0x1D4F5386, 0xA9B04F7C, 0x6E98A861, 0xEFADEBA6,
    0x900E1EC8, 0xB290DBCE, 0x05946814, 0xB83A01CE, 0x4EEC86BD, 0xAE836C6C,
    0x20182AAE, 0x4476F6F4, 0x7C4A0A31, 0x7D2809BA, 0x367B29B9, 0x42444BEA,
    0xDFD6025C, 0x1E665207, 0x18E0895B, 0x20D435DB, 0xC509A6D6, 0x8CC19AB1,
    0xA5D39BD2, 0xAB479AD5, 0x5786D029, 0x2E4B7CD7, 0xB77A3D76, 0xE2A09962,
};

status_t handle_hmac(ujson_t *uj) {
  // Declare test arguments
  cryptotest_hmac_hash_alg_t uj_hash_alg;
  cryptotest_hmac_key_t uj_key;
  cryptotest_hmac_message_t uj_message;
  // Deserialize test arguments from UART
  TRY(ujson_deserialize_cryptotest_hmac_hash_alg_t(uj, &uj_hash_alg));
  TRY(ujson_deserialize_cryptotest_hmac_key_t(uj, &uj_key));
  TRY(ujson_deserialize_cryptotest_hmac_message_t(uj, &uj_message));

  otcrypto_key_mode_t key_mode;
  unsigned int tag_bytes;
  switch (uj_hash_alg) {
    case kCryptotestHmacHashAlgSha256:
      key_mode = kOtcryptoKeyModeHmacSha256;
      tag_bytes = kOtcryptoHmacTagBytesSha256;
      break;
    case kCryptotestHmacHashAlgSha384:
      key_mode = kOtcryptoKeyModeHmacSha384;
      tag_bytes = kOtcryptoHmacTagBytesSha384;
      break;
    case kCryptotestHmacHashAlgSha512:
      key_mode = kOtcryptoKeyModeHmacSha512;
      tag_bytes = kOtcryptoHmacTagBytesSha512;
      break;
    default:
      LOG_ERROR("Unsupported HMAC key mode: %d", uj_hash_alg);
      return INVALID_ARGUMENT();
  }
  // Build the key configuration
  otcrypto_key_config_t config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = key_mode,
      .key_length = uj_key.key_len,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  // Create key shares.
  uint32_t key_buf[ceil_div(uj_key.key_len, sizeof(uint32_t))];
  memcpy(key_buf, uj_key.key, uj_key.key_len);
  for (size_t i = 0; i < ARRAYSIZE(key_buf); i++) {
    key_buf[i] ^= kTestMask[i];
  }
  otcrypto_const_word32_buf_t share0 = {
      .data = key_buf,
      .len = ARRAYSIZE(key_buf),
  };
  otcrypto_const_word32_buf_t share1 = {
      .data = kTestMask,
      .len = ARRAYSIZE(key_buf),
  };
  // Create blinded key
  uint32_t keyblob[2 * ARRAYSIZE(key_buf)];
  otcrypto_blinded_key_t key = {
      .config = config,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  TRY(otcrypto_import_blinded_key(share0, share1, &key));

  // Create input message
  uint8_t msg_buf[uj_message.message_len];
  memcpy(msg_buf, uj_message.message, uj_message.message_len);
  otcrypto_const_byte_buf_t input_message = {
      .len = uj_message.message_len,
      .data = msg_buf,
  };

  // Create tag
  uint32_t tag_buf[MaxTagWords];
  otcrypto_word32_buf_t tag = {
      .len = tag_bytes / sizeof(uint32_t),
      .data = tag_buf,
  };
  otcrypto_status_t status = otcrypto_hmac(&key, input_message, tag);
  if (status.value != kOtcryptoStatusValueOk) {
    return INTERNAL(status.value);
  }
  // Copy tag to uJSON type
  cryptotest_hmac_tag_t uj_tag;
  memcpy(uj_tag.tag, tag_buf, tag_bytes);
  uj_tag.tag_len = tag_bytes;

  // Send tag to host via UART
  RESP_OK(ujson_serialize_cryptotest_hmac_tag_t, uj, &uj_tag);
  return OK_STATUS(0);
}
