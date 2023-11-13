// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/aes.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/crypto/cryptotest/json/aes_commands.h"

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

status_t handle_aes_block(ujson_t *uj) {
  cryptotest_aes_mode_t uj_mode;
  cryptotest_aes_operation_t uj_op;
  cryptotest_aes_padding_t uj_padding;
  cryptotest_aes_data_t uj_data;
  TRY(ujson_deserialize_cryptotest_aes_mode_t(uj, &uj_mode));
  TRY(ujson_deserialize_cryptotest_aes_operation_t(uj, &uj_op));
  TRY(ujson_deserialize_cryptotest_aes_padding_t(uj, &uj_padding));
  TRY(ujson_deserialize_cryptotest_aes_data_t(uj, &uj_data));

  block_cipher_mode_t mode;
  key_mode_t key_mode;
  switch (uj_mode) {
    case kCryptotestAesModeEcb:
      mode = kBlockCipherModeEcb;
      key_mode = kKeyModeAesEcb;
      break;
    case kCryptotestAesModeCbc:
      mode = kBlockCipherModeCbc;
      key_mode = kKeyModeAesCbc;
      break;
    case kCryptotestAesModeCfb:
      mode = kBlockCipherModeCfb;
      key_mode = kKeyModeAesCfb;
      break;
    case kCryptotestAesModeOfb:
      mode = kBlockCipherModeOfb;
      key_mode = kKeyModeAesOfb;
      break;
    case kCryptotestAesModeCtr:
      mode = kBlockCipherModeCtr;
      key_mode = kKeyModeAesCtr;
      break;
    default:
      LOG_ERROR("Unrecognized AES block cipher mode: %d", uj_mode);
      return INVALID_ARGUMENT();
  }

  aes_operation_t op;
  switch (uj_op) {
    case kCryptotestAesOperationEncrypt:
      op = kAesOperationEncrypt;
      break;
    case kCryptotestAesOperationDecrypt:
      op = kAesOperationDecrypt;
      break;
    default:
      LOG_ERROR("Unrecognized AES operation: %d", uj_op);
      return INVALID_ARGUMENT();
  }

  aes_padding_t padding;
  switch (uj_padding) {
    case kCryptotestAesPaddingPkcs7:
      padding = kAesPaddingPkcs7;
      break;
    case kCryptotestAesPaddingIso9797M2:
      padding = kAesPaddingIso9797M2;
      break;
    case kCryptotestAesPaddingNull:
      padding = kAesPaddingNull;
      break;
    default:
      LOG_ERROR("Unrecognized AES padding scheme: %d", uj_op);
      return INVALID_ARGUMENT();
  }

  // Convert the data struct into cryptolib types
  const size_t AES_IV_SIZE = 4;
  uint32_t iv_buf[AES_IV_SIZE];
  memcpy(iv_buf, uj_data.iv, AES_IV_SIZE * 4);
  crypto_word32_buf_t iv = {
      .data = iv_buf,
      .len = kAesBlockWords,
  };

  crypto_const_byte_buf_t input = {
      .data = uj_data.input,
      .len = (size_t)uj_data.input_len,
  };

  // Build the key configuration
  crypto_key_config_t config = {
      .version = kCryptoLibVersion1,
      .key_mode = key_mode,
      .key_length = uj_data.key_length,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kSecurityLevelLow,
  };
  // Create buffer to store key
  uint32_t key_buf[kAesMaxKeyWords];
  memcpy(key_buf, uj_data.key, kAesMaxKeyBytes);
  // Create keyblob
  uint32_t keyblob[keyblob_num_words(config)];
  // Create blinded key
  TRY(keyblob_from_key_and_mask(key_buf, kKeyMask, config, keyblob));
  crypto_blinded_key_t key = {
      .config = config,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  key.checksum = integrity_blinded_checksum(&key);

  size_t padded_len_bytes;
  otcrypto_aes_padded_plaintext_length((size_t)uj_data.input_len, padding,
                                       &padded_len_bytes);
  if (padded_len_bytes > AES_CMD_MAX_MSG_BYTES) {
    return OUT_OF_RANGE();
  }
  uint32_t output_buf[padded_len_bytes / sizeof(uint32_t)];
  crypto_byte_buf_t output = {
      .data = (unsigned char *)output_buf,
      .len = sizeof(output_buf),
  };

  otcrypto_aes(&key, iv, mode, op, input, padding, output);

  cryptotest_aes_output_t uj_output;
  uj_output.output_len = padded_len_bytes;
  memset(uj_output.output, 0, AES_CMD_MAX_MSG_BYTES);
  memcpy(uj_output.output, output_buf, uj_output.output_len);
  RESP_OK(ujson_serialize_cryptotest_aes_output_t, uj, &uj_output);
  return OK_STATUS(0);
}

status_t handle_aes(ujson_t *uj) {
  aes_subcommand_t cmd;
  TRY(ujson_deserialize_aes_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kAesSubcommandAesBlock:
      return handle_aes_block(uj);
      break;
    default:
      LOG_ERROR("Unrecognized AES subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS(0);
}
