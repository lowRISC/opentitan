// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/aes_gcm.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/aes_gcm.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/rand_testutils.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/crypto/cryptotest/json/aes_gcm_commands.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('m', 'c', 'g')

enum {
  kAesBlockBytes = 128 / 8,
  kAesBlockWords = kAesBlockBytes / sizeof(uint32_t),
  kAesMaxKeyBytes = 256 / 8,
  kAesMaxKeyWords = kAesMaxKeyBytes / 4,
};

// Arbitrary mask for testing (borrowed from aes_functest.c).
static const uint32_t kKeyMask[8] = {
    0x1b81540c, 0x220733c9, 0x8bf85383, 0x05ab50b4,
    0x8acdcb7e, 0x15e76440, 0x8459b2ce, 0xdc2110cc,
};

// Available security levels. The test randomly chooses one.
static const otcrypto_key_security_level_t security_level[3] = {
    kOtcryptoKeySecurityLevelLow,
    kOtcryptoKeySecurityLevelMedium,
    kOtcryptoKeySecurityLevelHigh,
};

status_t handle_aes_gcm_op(ujson_t *uj) {
  cryptotest_aes_gcm_operation_t uj_op;
  cryptotest_aes_gcm_data_t uj_data;
  TRY(ujson_deserialize_cryptotest_aes_gcm_operation_t(uj, &uj_op));
  TRY(ujson_deserialize_cryptotest_aes_gcm_data_t(uj, &uj_data));

  // Encryption or decryption
  bool op_enc;
  switch (uj_op) {
    case kCryptotestAesGcmOperationEncrypt:
      op_enc = true;
      break;
    case kCryptotestAesGcmOperationDecrypt:
      op_enc = false;
      break;
    default:
      LOG_ERROR("Unrecognized AES operation: %d", uj_op);
      return INVALID_ARGUMENT();
  }

  // Tag length.
  otcrypto_aes_gcm_tag_len_t tag_len;
  size_t tag_num_words;
  switch (uj_data.tag_length) {
    case (128 / 8):
      tag_len = kOtcryptoAesGcmTagLen128;
      tag_num_words = 4;
      break;
    case (96 / 8):
      tag_len = kOtcryptoAesGcmTagLen96;
      tag_num_words = 3;
      break;
    case (64 / 8):
      tag_len = kOtcryptoAesGcmTagLen64;
      tag_num_words = 2;
      break;
    case (32 / 8):
      tag_len = kOtcryptoAesGcmTagLen32;
      tag_num_words = 1;
      break;
    default:
      LOG_ERROR("Unrecognized AES-GCM tag length: %d", uj_data.tag_length);
      return INVALID_ARGUMENT();
  }

  // IV length. Only support 96- and 128-bit IV length.
  size_t iv_num_words;
  switch (uj_data.iv_length) {
    case (12):
      iv_num_words = 3;
      break;
    case (16):
      iv_num_words = 4;
      break;
    default:
      LOG_ERROR("Unrecognized AES-GCM IV length: %d", uj_data.iv_length);
      return INVALID_ARGUMENT();
  }

  // Convert the data struct into cryptolib types
  uint32_t iv_buf[iv_num_words];
  memcpy(iv_buf, uj_data.iv, uj_data.iv_length);
  otcrypto_const_word32_buf_t iv = {
      .data = iv_buf,
      .len = iv_num_words,
  };

  otcrypto_const_byte_buf_t input = {
      .data = uj_data.input,
      .len = (size_t)uj_data.input_length,
  };

  otcrypto_const_byte_buf_t aad = {
      .data = uj_data.aad,
      .len = uj_data.aad_length,
  };

  // Select a random security level.
  size_t sec_lvl_idx = rand_testutils_gen32_range(
      /*min=*/0, /*max=*/ARRAYSIZE(security_level) - 1);

  // Build the key configuration
  otcrypto_key_config_t config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeAesGcm,
      .key_length = uj_data.key_length,
      .hw_backed = kHardenedBoolFalse,
      .security_level = security_level[sec_lvl_idx],
  };

  // Create buffer to store key
  uint32_t key_buf[kAesMaxKeyWords];
  memcpy(key_buf, uj_data.key, kAesMaxKeyBytes);
  // Create keyblob
  uint32_t keyblob[keyblob_num_words(config)];
  // Create blinded key
  TRY(keyblob_from_key_and_mask(key_buf, kKeyMask, config, keyblob));
  otcrypto_blinded_key_t key = {
      .config = config,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  key.checksum = integrity_blinded_checksum(&key);

  uint8_t output_data[AES_GCM_CMD_MAX_MSG_BYTES];
  otcrypto_byte_buf_t output = {
      .data = output_data,
      .len = uj_data.input_length,
  };

  uint32_t tag_data[tag_num_words];

  hardened_bool_t tag_valid = kHardenedBoolTrue;

  if (op_enc) {
    otcrypto_word32_buf_t tag = {
        .data = tag_data,
        .len = tag_num_words,
    };
    TRY(otcrypto_aes_gcm_encrypt(&key, input, iv, aad, tag_len, output, tag));
  } else {
    memcpy(tag_data, uj_data.tag, uj_data.tag_length);
    otcrypto_const_word32_buf_t tag = {
        .data = tag_data,
        .len = tag_num_words,
    };
    TRY(otcrypto_aes_gcm_decrypt(&key, input, iv, aad, tag_len, tag, output,
                                 &tag_valid));
  }

  cryptotest_aes_gcm_output_t uj_output;
  uj_output.output_len = uj_data.input_length;
  memset(uj_output.output, 0, AES_GCM_CMD_MAX_MSG_BYTES);
  memcpy(uj_output.output, output_data, uj_output.output_len);

  uj_output.tag_len = uj_data.tag_length;
  memset(uj_output.tag, 0, AES_GCM_CMD_MAX_TAG_BYTES);
  memcpy(uj_output.tag, tag_data, uj_output.tag_len);

  if (tag_valid == kHardenedBoolTrue) {
    uj_output.tag_valid = true;
  } else {
    uj_output.tag_valid = false;
  }

  RESP_OK(ujson_serialize_cryptotest_aes_gcm_output_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_aes_gcm(ujson_t *uj) {
  aes_gcm_subcommand_t cmd;
  TRY(ujson_deserialize_aes_gcm_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kAesGcmSubcommandAesGcmOp:
      return handle_aes_gcm_op(uj);
      break;
    default:
      LOG_ERROR("Unrecognized AES GCM subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
