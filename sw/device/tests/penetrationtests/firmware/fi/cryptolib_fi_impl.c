// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/fi/cryptolib_fi_impl.h"

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
#include "sw/device/tests/penetrationtests/json/cryptolib_fi_commands.h"

status_t cryptolib_fi_aes_impl(cryptolib_fi_aes_in_t uj_input,
                               cryptolib_fi_aes_out_t *uj_output) {
  // Set the AES mode.
  otcrypto_aes_mode_t mode;
  otcrypto_key_mode_t key_mode;
  switch (uj_input.mode) {
    case kPentestAesModeEcb:
      mode = kOtcryptoAesModeEcb;
      key_mode = kOtcryptoKeyModeAesEcb;
      break;
    case kPentestAesModeCbc:
      mode = kOtcryptoAesModeCbc;
      key_mode = kOtcryptoKeyModeAesCbc;
      break;
    case kPentestAesModeCfb:
      mode = kOtcryptoAesModeCfb;
      key_mode = kOtcryptoKeyModeAesCfb;
      break;
    case kPentestAesModeOfb:
      mode = kOtcryptoAesModeOfb;
      key_mode = kOtcryptoKeyModeAesOfb;
      break;
    case kPentestAesModeCtr:
      mode = kOtcryptoAesModeCtr;
      key_mode = kOtcryptoKeyModeAesCtr;
      break;
    default:
      LOG_ERROR("Unrecognized AES block cipher mode: %d", uj_input.mode);
      return INVALID_ARGUMENT();
  }

  // Set operation.
  otcrypto_aes_operation_t op;
  if (uj_input.op_enc) {
    op = kOtcryptoAesOperationEncrypt;
  } else {
    op = kOtcryptoAesOperationDecrypt;
  }

  // Set padding.
  otcrypto_aes_padding_t padding;
  switch (uj_input.padding) {
    case kPentestAesPaddingPkcs7:
      padding = kOtcryptoAesPaddingPkcs7;
      break;
    case kPentestAesPaddingIso9797M2:
      padding = kOtcryptoAesPaddingIso9797M2;
      break;
    case kPentestAesPaddingNull:
      padding = kOtcryptoAesPaddingNull;
      break;
    default:
      LOG_ERROR("Unrecognized AES padding scheme: %d", uj_input.padding);
      return INVALID_ARGUMENT();
  }

  // Convert the data struct into cryptolib types.
  uint32_t iv_buf[kPentestAesIvSize];
  memcpy(iv_buf, uj_input.iv, sizeof(uj_input.iv));
  otcrypto_word32_buf_t iv = {
      .data = iv_buf,
      .len = kPentestAesBlockWords,
  };

  otcrypto_const_byte_buf_t input = {
      .data = uj_input.data,
      .len = uj_input.data_len,
  };

  // Build the key configuration.
  otcrypto_key_config_t config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = key_mode,
      .key_length = uj_input.key_len,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };

  // Create buffer to store key.
  uint32_t key_buf[kPentestAesMaxKeyWords];
  memset(key_buf, 0, AES_CMD_MAX_KEY_BYTES);
  memcpy(key_buf, uj_input.key, sizeof(uj_input.key));
  // Create keyblob.
  uint32_t keyblob[keyblob_num_words(config)];
  // Create blinded key.
  TRY(keyblob_from_key_and_mask(key_buf, kAesKeyMask, config, keyblob));
  otcrypto_blinded_key_t key = {
      .config = config,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  key.checksum = integrity_blinded_checksum(&key);

  size_t padded_len_bytes;
  otcrypto_aes_padded_plaintext_length(uj_input.data_len, padding,
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
  otcrypto_aes(&key, iv, mode, op, input, padding, output);
  pentest_set_trigger_low();

  // Return data back to host.
  uj_output->data_len = padded_len_bytes;
  uj_output->cfg = 0;
  memset(uj_output->data, 0, AES_CMD_MAX_MSG_BYTES);
  memcpy(uj_output->data, output_buf, uj_output->data_len);

  return OK_STATUS();
}
