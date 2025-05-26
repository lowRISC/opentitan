// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/kmac.h"

#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/key_transport.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/crypto/cryptotest/json/kmac_commands.h"

const int MaxCustomizationStringBytes = 36;

const int MaxKmacTagBytes = 64;
const int MaxKmacTagWords = MaxKmacTagBytes / sizeof(uint32_t);

const unsigned int kOtcryptoKmacTagBytesKmac128 = 32;
const unsigned int kOtcryptoKmacTagBytesKmac256 = 64;

// Random value for masking, as large as the longest test key. This value
// should not affect the result.
static const uint32_t kTestMask[48] = {
    0x61A5D83D, 0x55D6B114, 0xFD2771B8, 0xF70CB89D, 0x342A1205, 0x03571376,
    0xA23651E3, 0xD246D8E6, 0x9A6AAAA0, 0x105880E2, 0x0C22EA57, 0xB86D07D5,
    0x6BAA9320, 0xD09F20D8, 0xE9A4520E, 0xEB0BA531, 0x19FEBE66, 0xEAEA1CF1,
    0x3618EFF5, 0x66FB71DC, 0x703A9932, 0x8C7C7807, 0xFA5D68E5, 0x8364B8C5,
    0x5BAFF5E7, 0x32BDD917, 0x66254D17, 0xABAB9FD4, 0x7FAE4EE8, 0x3D1F7A0D,
    0x00C2C8A6, 0xC6ED700E, 0xD86D283C, 0xD6753A6E, 0x0555D290, 0x08C0DA0A,
    0x9F18BE27, 0x263EA1FC, 0xCA8D6517, 0x88156B88, 0xE6BE966E, 0xD6D8E410,
    0x2E5A7583, 0xDDB18102, 0x0C9157A7, 0x8437AA66, 0x88EF488A, 0x45A1B1B1,
};

status_t handle_kmac(ujson_t *uj) {
  // Declare test arguments
  cryptotest_kmac_mode_t uj_mode;
  cryptotest_kmac_required_tag_length_t uj_required_tag_length;
  cryptotest_kmac_key_t uj_key;
  cryptotest_kmac_message_t uj_message;
  cryptotest_kmac_customization_string_t uj_customization_string;
  // Deserialize test arguments from UART
  TRY(ujson_deserialize_cryptotest_kmac_mode_t(uj, &uj_mode));
  TRY(ujson_deserialize_cryptotest_kmac_required_tag_length_t(
      uj, &uj_required_tag_length));
  TRY(ujson_deserialize_cryptotest_kmac_key_t(uj, &uj_key));
  TRY(ujson_deserialize_cryptotest_kmac_message_t(uj, &uj_message));
  TRY(ujson_deserialize_cryptotest_kmac_customization_string_t(
      uj, &uj_customization_string));

  otcrypto_key_mode_t key_mode;
  switch (uj_mode) {
    case kCryptotestKmacModeKmac128:
      key_mode = kOtcryptoKeyModeKmac128;
      break;
    case kCryptotestKmacModeKmac256:
      key_mode = kOtcryptoKeyModeKmac256;
      break;
    default:
      LOG_ERROR("Unsupported KMAC mode: %d", uj_mode);
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

  // Create customization string
  uint8_t customization_string_buf[uj_customization_string
                                       .customization_string_len];
  memcpy(customization_string_buf, uj_customization_string.customization_string,
         uj_customization_string.customization_string_len);
  otcrypto_const_byte_buf_t customization_string = {
      .len = uj_customization_string.customization_string_len,
      .data = customization_string_buf,
  };

  // Create tag
  uint32_t tag_buf[MaxKmacTagWords];
  otcrypto_word32_buf_t tag = {
      .len = uj_required_tag_length.required_tag_length / sizeof(uint32_t),
      .data = tag_buf,
  };
  otcrypto_status_t status =
      otcrypto_kmac(&key, input_message, customization_string,
                    uj_required_tag_length.required_tag_length, tag);
  if (status.value != kOtcryptoStatusValueOk) {
    return INTERNAL(status.value);
  }
  // Copy tag to uJSON type
  cryptotest_kmac_tag_t uj_tag;
  memcpy(uj_tag.tag, tag_buf, uj_required_tag_length.required_tag_length);
  uj_tag.tag_len = uj_required_tag_length.required_tag_length;

  // Send tag to host via UART
  RESP_OK(ujson_serialize_cryptotest_kmac_tag_t, uj, &uj_tag);
  return OK_STATUS(0);
}
