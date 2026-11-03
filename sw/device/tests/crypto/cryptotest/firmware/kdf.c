// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/crypto/cryptotest/firmware/kdf.h"

#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/include/cryptolib_build_info.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/hkdf.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/kdf_ctr.h"
#include "sw/device/lib/crypto/include/key_transport.h"
#include "sw/device/lib/crypto/include/kmac_kdf.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/crypto/cryptotest/json/kdf_commands.h"
#include "sw/device/tests/crypto/lib/crypto_test_lib.h"

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

status_t handle_kdf(ujson_t *uj) {
  cryptotest_kdf_algorithm_t uj_algorithm;
  cryptotest_kdf_mode_t uj_mode;
  cryptotest_kdf_required_output_length_t uj_required_output_length;
  cryptotest_kdf_key_t uj_key;
  cryptotest_kdf_label_t uj_label;
  cryptotest_kdf_context_t uj_context;

  TRY(ujson_deserialize_cryptotest_kdf_algorithm_t(uj, &uj_algorithm));
  TRY(ujson_deserialize_cryptotest_kdf_mode_t(uj, &uj_mode));
  TRY(ujson_deserialize_cryptotest_kdf_required_output_length_t(
      uj, &uj_required_output_length));
  TRY(ujson_deserialize_cryptotest_kdf_key_t(uj, &uj_key));
  TRY(ujson_deserialize_cryptotest_kdf_label_t(uj, &uj_label));
  TRY(ujson_deserialize_cryptotest_kdf_context_t(uj, &uj_context));

  size_t req_out_len = uj_required_output_length.required_output_length;
  if (req_out_len == 0 || req_out_len > KDF_CMD_MAX_OUTPUT_BYTES) {
    LOG_ERROR("Unsupported KDF output length: %u", req_out_len);
    return INVALID_ARGUMENT();
  }
  if (uj_key.key_len == 0 || uj_key.key_len > KDF_CMD_MAX_KEY_BYTES) {
    LOG_ERROR("Unsupported KDF key length: %u", uj_key.key_len);
    return INVALID_ARGUMENT();
  }

  otcrypto_key_mode_t input_key_mode;
  switch (uj_algorithm) {
    case kCryptotestKdfAlgorithmHkdf:
    case kCryptotestKdfAlgorithmKdfCtr:
      switch (uj_mode) {
        case kCryptotestKdfModeSha256:
          input_key_mode = kOtcryptoKeyModeHmacSha256;
          break;
        case kCryptotestKdfModeSha384:
          input_key_mode = kOtcryptoKeyModeHmacSha384;
          break;
        case kCryptotestKdfModeSha512:
          input_key_mode = kOtcryptoKeyModeHmacSha512;
          break;
        default:
          LOG_ERROR("Unsupported HMAC KDF mode: %d", uj_mode);
          return INVALID_ARGUMENT();
      }
      break;
    case kCryptotestKdfAlgorithmKmacKdf:
      switch (uj_mode) {
        case kCryptotestKdfModeKmac128:
          input_key_mode = kOtcryptoKeyModeKdfKmac128;
          break;
        case kCryptotestKdfModeKmac256:
          input_key_mode = kOtcryptoKeyModeKdfKmac256;
          break;
        default:
          LOG_ERROR("Unsupported KMAC KDF mode: %d", uj_mode);
          return INVALID_ARGUMENT();
      }
      break;
    default:
      LOG_ERROR("Unsupported KDF algorithm: %d", uj_algorithm);
      return INVALID_ARGUMENT();
  }

  otcrypto_key_security_level_t sec_level;
  TRY(determine_security_level(&sec_level));

  otcrypto_key_config_t input_config = {
      .version = otcrypto_lib_version(),
      .key_mode = input_key_mode,
      .key_length = uj_key.key_len,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = sec_level,
  };

  size_t key_words = ceil_div(uj_key.key_len, sizeof(uint32_t));
  uint32_t key_buf[key_words];
  memset(key_buf, 0, sizeof(key_buf));
  memcpy(key_buf, uj_key.key, uj_key.key_len);
  for (size_t i = 0; i < key_words; i++) {
    key_buf[i] ^= kTestMask[i];
  }

  otcrypto_const_word32_buf_t share0 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, key_buf, key_words);
  otcrypto_const_word32_buf_t share1 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, kTestMask, key_words);

  uint32_t input_keyblob[2 * key_words];
  otcrypto_blinded_key_t input_key = {
      .config = input_config,
      .keyblob_length = sizeof(input_keyblob),
      .keyblob = input_keyblob,
  };
  TRY(otcrypto_import_blinded_key(&share0, &share1, &input_key));

  size_t label_len = uj_label.label_len;
  uint8_t label_buf[label_len > 0 ? label_len : 1];
  if (label_len > 0) {
    memcpy(label_buf, uj_label.label, label_len);
  }
  otcrypto_const_byte_buf_t label =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, label_buf, label_len);

  size_t context_len = uj_context.context_len;
  uint8_t context_buf[context_len > 0 ? context_len : 1];
  if (context_len > 0) {
    memcpy(context_buf, uj_context.context, context_len);
  }
  otcrypto_const_byte_buf_t context =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, context_buf, context_len);

  size_t output_words = ceil_div(req_out_len, sizeof(uint32_t));
  uint32_t output_keyblob[2 * output_words];
  memset(output_keyblob, 0, sizeof(output_keyblob));
  otcrypto_blinded_key_t output_key = {
      .config =
          {
              .version = otcrypto_lib_version(),
              .key_mode = kOtcryptoKeyModeAesCtr,
              .key_length = req_out_len,
              .hw_backed = kHardenedBoolFalse,
              .exportable = kHardenedBoolTrue,
              .security_level = sec_level,
          },
      .keyblob_length = sizeof(output_keyblob),
      .keyblob = output_keyblob,
  };

  otcrypto_status_t status;
  switch (uj_algorithm) {
    case kCryptotestKdfAlgorithmHkdf:
      status = otcrypto_hkdf(&input_key, &label, &context, &output_key);
      break;
    case kCryptotestKdfAlgorithmKmacKdf:
      status = otcrypto_kmac_kdf(&input_key, &label, &context, &output_key);
      break;
    case kCryptotestKdfAlgorithmKdfCtr:
      status = otcrypto_kdf_ctr_hmac(&input_key, &label, &context, &output_key);
      break;
    default:
      return INVALID_ARGUMENT();
  }
  if (status.value != kOtcryptoStatusValueOk) {
    return INTERNAL(status.value);
  }

  uint32_t out_share0[output_words];
  uint32_t out_share1[output_words];
  otcrypto_word32_buf_t out_share0_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, out_share0, output_words);
  otcrypto_word32_buf_t out_share1_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, out_share1, output_words);
  TRY(otcrypto_export_blinded_key(&output_key, &out_share0_buf,
                                  &out_share1_buf));

  uint32_t unmasked_output[output_words];
  for (size_t i = 0; i < output_words; i++) {
    unmasked_output[i] = out_share0[i] ^ out_share1[i];
  }

  cryptotest_kdf_output_t uj_output;
  memset(&uj_output, 0, sizeof(uj_output));
  memcpy(uj_output.output, unmasked_output, req_out_len);
  uj_output.output_len = req_out_len;

  RESP_OK(ujson_serialize_cryptotest_kdf_output_t, uj, &uj_output);
  return OK_STATUS(0);
}
