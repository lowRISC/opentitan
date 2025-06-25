// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/sca/cryptolib_sca_impl.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/aes.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/tests/penetrationtests/firmware/lib/cryptolib.h"
#include "sw/device/tests/penetrationtests/firmware/lib/pentest_lib.h"
#include "sw/device/tests/penetrationtests/json/cryptolib_sca_sym_commands.h"

status_t cryptolib_sca_aes_impl(uint8_t data_in[AES_CMD_MAX_MSG_BYTES],
                                size_t data_in_len,
                                uint8_t key[AES_CMD_MAX_KEY_BYTES],
                                size_t key_len,
                                uint8_t iv[AES_CMD_MAX_BLOCK_BYTES],
                                uint8_t data_out[AES_CMD_MAX_MSG_BYTES],
                                size_t *data_out_len, size_t padding,
                                size_t mode, bool op_enc, size_t cfg_in,
                                size_t *cfg_out, size_t trigger) {
  // Set the AES mode.
  otcrypto_aes_mode_t aes_mode;
  otcrypto_key_mode_t key_mode;
  switch (mode) {
    case kPentestAesModeEcb:
      aes_mode = kOtcryptoAesModeEcb;
      key_mode = kOtcryptoKeyModeAesEcb;
      break;
    case kPentestAesModeCbc:
      aes_mode = kOtcryptoAesModeCbc;
      key_mode = kOtcryptoKeyModeAesCbc;
      break;
    case kPentestAesModeCfb:
      aes_mode = kOtcryptoAesModeCfb;
      key_mode = kOtcryptoKeyModeAesCfb;
      break;
    case kPentestAesModeOfb:
      aes_mode = kOtcryptoAesModeOfb;
      key_mode = kOtcryptoKeyModeAesOfb;
      break;
    case kPentestAesModeCtr:
      aes_mode = kOtcryptoAesModeCtr;
      key_mode = kOtcryptoKeyModeAesCtr;
      break;
    default:
      LOG_ERROR("Unrecognized AES block cipher mode: %d", mode);
      return INVALID_ARGUMENT();
  }

  // Set operation.
  otcrypto_aes_operation_t op;
  if (op_enc) {
    op = kOtcryptoAesOperationEncrypt;
  } else {
    op = kOtcryptoAesOperationDecrypt;
  }

  // Set padding.
  otcrypto_aes_padding_t aes_padding;
  switch (padding) {
    case kPentestAesPaddingPkcs7:
      aes_padding = kOtcryptoAesPaddingPkcs7;
      break;
    case kPentestAesPaddingIso9797M2:
      aes_padding = kOtcryptoAesPaddingIso9797M2;
      break;
    case kPentestAesPaddingNull:
      aes_padding = kOtcryptoAesPaddingNull;
      break;
    default:
      LOG_ERROR("Unrecognized AES padding scheme: %d", padding);
      return INVALID_ARGUMENT();
  }

  // Convert the data struct into cryptolib types.
  uint32_t iv_buf[kPentestAesIvSize];
  memcpy(iv_buf, iv, sizeof(iv_buf));
  otcrypto_word32_buf_t aes_iv = {
      .data = iv_buf,
      .len = kPentestAesBlockWords,
  };

  otcrypto_const_byte_buf_t input = {
      .data = data_in,
      .len = data_in_len,
  };

  // Build the key configuration.
  otcrypto_key_config_t config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = key_mode,
      .key_length = key_len,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };

  // Create buffer to store key.
  uint32_t key_buf[kPentestAesMaxKeyWords];
  memset(key_buf, 0, AES_CMD_MAX_KEY_BYTES);
  memcpy(key_buf, key, sizeof(key_buf));
  // Create keyblob.
  uint32_t keyblob[keyblob_num_words(config)];
  // Create blinded key.
  TRY(keyblob_from_key_and_mask(key_buf, kAesKeyMask, config, keyblob));
  otcrypto_blinded_key_t aes_key = {
      .config = config,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  aes_key.checksum = integrity_blinded_checksum(&aes_key);

  size_t padded_len_bytes;
  otcrypto_aes_padded_plaintext_length(data_in_len, aes_padding,
                                       &padded_len_bytes);

  if (padded_len_bytes > AES_CMD_MAX_MSG_BYTES) {
    return OUT_OF_RANGE();
  }
  uint32_t output_buf[padded_len_bytes / sizeof(uint32_t)];
  otcrypto_byte_buf_t output = {
      .data = (unsigned char *)output_buf,
      .len = sizeof(output_buf),
  };

  // Trigger window.
  pentest_set_trigger_high();
  otcrypto_aes(&aes_key, aes_iv, aes_mode, op, input, aes_padding, output);
  pentest_set_trigger_low();

  // Return data back to host.
  *data_out_len = padded_len_bytes;
  *cfg_out = 0;
  memset(data_out, 0, AES_CMD_MAX_MSG_BYTES);
  memcpy(data_out, output_buf, padded_len_bytes);

  return OK_STATUS();
}
