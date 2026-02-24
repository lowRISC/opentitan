// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/sca/cryptolib_sca_sym_impl.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/aes.h"
#include "sw/device/lib/crypto/include/aes_gcm.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/drbg.h"
#include "sw/device/lib/crypto/include/hmac.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/tests/penetrationtests/firmware/lib/cryptolib_sym.h"
#include "sw/device/tests/penetrationtests/firmware/lib/pentest_lib.h"
#include "sw/device/tests/penetrationtests/json/cryptolib_sca_sym_commands.h"

#define MODULE_ID MAKE_MODULE_ID('c', 's', 'i')

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
  otcrypto_word32_buf_t aes_iv =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, iv_buf, kPentestAesBlockWords);
  memcpy(iv_buf, iv, sizeof(iv_buf));

  otcrypto_const_byte_buf_t input =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, data_in, data_in_len);

  // Build the key configuration.
  otcrypto_key_config_t config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = key_mode,
      .key_length = key_len,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelHigh,
  };

  // Create buffer to store key.
  uint32_t key_buf[kPentestAesMaxKeyWords];
  memset(key_buf, 0, AES_CMD_MAX_KEY_BYTES);
  memcpy(key_buf, key, sizeof(key_buf));
  // Create keyblob.
  uint32_t keyblob[keyblob_num_words(config)];
  // Create blinded key.
  uint32_t aes_key_mask[kPentestAesMaxKeyWords];
  memset(aes_key_mask, 0, AES_CMD_MAX_KEY_BYTES);
  for (size_t it = 0; it < kPentestAesMaxKeyWords; it++) {
    aes_key_mask[it] = pentest_ibex_rnd32_read();
  }
  HARDENED_TRY(
      keyblob_from_key_and_mask(key_buf, aes_key_mask, config, keyblob));
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
  otcrypto_byte_buf_t output = OTCRYPTO_MAKE_BUF(
      otcrypto_byte_buf_t, (unsigned char *)output_buf, sizeof(output_buf));

  // Trigger window.
  pentest_set_trigger_high();
  HARDENED_TRY(
      otcrypto_aes(&aes_key, aes_iv, aes_mode, op, input, aes_padding, output));
  pentest_set_trigger_low();

  // Return data back to host.
  *data_out_len = padded_len_bytes;
  *cfg_out = 0;
  memset(data_out, 0, AES_CMD_MAX_MSG_BYTES);
  memcpy(data_out, output_buf, padded_len_bytes);

  return OK_STATUS();
}

status_t cryptolib_sca_drbg_generate_impl(
    uint8_t nonce[DRBG_CMD_MAX_NONCE_BYTES], size_t nonce_len,
    uint8_t data_out[DRBG_CMD_MAX_OUTPUT_BYTES], size_t data_out_len,
    size_t mode, size_t cfg_in, size_t *cfg_out, size_t trigger) {
  // Nonce buffer used for the generate command of the DRBG.
  uint8_t nonce_buf[nonce_len];
  memcpy(nonce_buf, nonce, nonce_len);

  otcrypto_const_byte_buf_t nonce_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, nonce_buf, nonce_len);

  // Buffer for the output entropy data.
  uint32_t output_data[data_out_len];
  otcrypto_word32_buf_t output = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, output_data, ARRAYSIZE(output_data));

  // Trigger window 0.
  if (trigger & kPentestTrigger2) {
    pentest_set_trigger_high();
  }
  HARDENED_TRY(otcrypto_drbg_generate(nonce_in, output));
  if (trigger & kPentestTrigger2) {
    pentest_set_trigger_low();
  }

  // Return data back to host.
  *cfg_out = 0;
  memset(data_out, 0, DRBG_CMD_MAX_OUTPUT_BYTES);
  memcpy(data_out, output_data, data_out_len);

  return OK_STATUS();
}

status_t cryptolib_sca_drbg_reseed_impl(
    uint8_t entropy[DRBG_CMD_MAX_ENTROPY_BYTES], size_t entropy_len,
    uint8_t nonce[DRBG_CMD_MAX_NONCE_BYTES], size_t nonce_len,
    size_t reseed_interval, size_t mode, size_t cfg_in, size_t *cfg_out,
    size_t trigger) {
  // Entropy buffer used for the instantiation of the DRBG.
  uint8_t entropy_buf[entropy_len];
  memcpy(entropy_buf, entropy, entropy_len);

  otcrypto_const_byte_buf_t entropy_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, entropy_buf, entropy_len);

  // Trigger window 0.
  if (trigger & kPentestTrigger1) {
    pentest_set_trigger_high();
  }
  HARDENED_TRY(otcrypto_drbg_instantiate(entropy_in));
  if (trigger & kPentestTrigger1) {
    pentest_set_trigger_low();
  }

  // Return data back to host.
  *cfg_out = 0;

  return OK_STATUS();
}

status_t cryptolib_sca_gcm_impl(
    uint8_t data_in[AES_CMD_MAX_MSG_BYTES], size_t data_in_len,
    uint8_t aad[AES_CMD_MAX_MSG_BYTES], size_t aad_len,
    uint8_t key[AES_CMD_MAX_KEY_BYTES], size_t key_len,
    uint8_t iv[AES_CMD_MAX_BLOCK_BYTES],
    uint8_t data_out[AES_CMD_MAX_MSG_BYTES], size_t *data_out_len,
    uint8_t tag[AES_CMD_MAX_MSG_BYTES], size_t *tag_len, size_t cfg_in,
    size_t *cfg_out, size_t trigger) {
  // Construct the blinded key configuration.
  otcrypto_key_config_t config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeAesGcm,
      .key_length = key_len,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelHigh,
  };

  // Construct blinded key from the key and mask.
  uint32_t key_buf[kPentestAesMaxKeyWords];
  memset(key_buf, 0, AES_CMD_MAX_KEY_BYTES);
  memcpy(key_buf, key, key_len);

  // Create random mask.
  uint32_t aes_key_mask[kPentestAesMaxKeyWords];
  memset(aes_key_mask, 0, AES_CMD_MAX_KEY_BYTES);
  for (size_t it = 0; it < kPentestAesMaxKeyWords; it++) {
    aes_key_mask[it] = pentest_ibex_rnd32_read();
  }

  uint32_t keyblob[keyblob_num_words(config)];
  HARDENED_TRY(
      keyblob_from_key_and_mask(key_buf, aes_key_mask, config, keyblob));

  // Construct the blinded key.
  otcrypto_blinded_key_t gcm_key = {
      .config = config,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
      .checksum = 0,
  };

  // Set the checksum.
  gcm_key.checksum = integrity_blinded_checksum(&gcm_key);

  // Prepare the input buffers.
  size_t iv_num_words = 4;
  uint32_t iv_data[iv_num_words];
  memcpy(iv_data, iv, sizeof(iv_data));
  otcrypto_const_word32_buf_t gcm_iv = {
      .data = iv_data,
      .len = iv_num_words,
  };
  otcrypto_const_byte_buf_t plaintext = {
      .data = data_in,
      .len = data_in_len,
  };
  otcrypto_const_byte_buf_t gcm_aad = {
      .data = aad,
      .len = aad_len,
  };

  size_t tag_num_words = (*tag_len + sizeof(uint32_t) - 1) / sizeof(uint32_t);
  uint32_t actual_tag_data[tag_num_words];
  otcrypto_word32_buf_t actual_tag = {
      .data = actual_tag_data,
      .len = tag_num_words,
  };

  uint8_t actual_ciphertext_data[AES_CMD_MAX_MSG_BYTES];
  otcrypto_byte_buf_t actual_ciphertext = {
      .data = actual_ciphertext_data,
      .len = data_in_len,
  };

  otcrypto_aes_gcm_tag_len_t gcm_tag_len;
  switch (*tag_len) {
    case (128 / 8):
      gcm_tag_len = kOtcryptoAesGcmTagLen128;
      break;
    case (96 / 8):
      gcm_tag_len = kOtcryptoAesGcmTagLen96;
      break;
    case (64 / 8):
      gcm_tag_len = kOtcryptoAesGcmTagLen64;
      break;
    case (32 / 8):
      gcm_tag_len = kOtcryptoAesGcmTagLen32;
      break;
    default:
      LOG_ERROR("Unrecognized AES-GCM tag length: %d", *tag_len);
      return INVALID_ARGUMENT();
  }

  // Trigger window.
  pentest_set_trigger_high();
  HARDENED_TRY(otcrypto_aes_gcm_encrypt(&gcm_key, plaintext, gcm_iv, gcm_aad,
                                        gcm_tag_len, actual_ciphertext,
                                        actual_tag));
  pentest_set_trigger_low();

  // Return data back to host.
  *cfg_out = 0;
  // Ciphertext.
  *data_out_len = data_in_len;
  memset(data_out, 0, AES_CMD_MAX_MSG_BYTES);
  memcpy(data_out, actual_ciphertext_data, *data_out_len);
  // Tag.
  memset(tag, 0, AES_CMD_MAX_MSG_BYTES);
  memcpy(tag, actual_tag_data, *tag_len);

  return OK_STATUS();
}

status_t cryptolib_sca_hmac_impl(uint8_t data_in[HMAC_CMD_MAX_MSG_BYTES],
                                 size_t data_in_len,
                                 uint8_t key[HMAC_CMD_MAX_KEY_BYTES],
                                 size_t key_len,
                                 uint8_t data_out[HMAC_CMD_MAX_TAG_BYTES],
                                 size_t *data_out_len, size_t hash_mode,
                                 size_t mode, size_t cfg_in, size_t *cfg_out,
                                 size_t trigger) {
  // Set the HMAC mode.
  otcrypto_key_mode_t key_mode;
  unsigned int tag_bytes;
  switch (mode) {
    case kPentestHmacHashAlgSha256:
      key_mode = kOtcryptoKeyModeHmacSha256;
      tag_bytes = kPentestHmacTagBytesSha256;
      break;
    case kPentestHmacHashAlgSha384:
      key_mode = kOtcryptoKeyModeHmacSha384;
      tag_bytes = kPentestHmacTagBytesSha384;
      break;
    case kPentestHmacHashAlgSha512:
      key_mode = kOtcryptoKeyModeHmacSha512;
      tag_bytes = kPentestHmacTagBytesSha512;
      break;
    default:
      LOG_ERROR("Unsupported HMAC key mode: %d", mode);
      return INVALID_ARGUMENT();
  }

  // Build the key configuration.
  otcrypto_key_config_t config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = key_mode,
      .key_length = key_len,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelHigh,
  };

  // Create buffer to store key.
  uint32_t key_buf[key_len];
  memcpy(key_buf, key, key_len);
  // Create keyblob.
  uint32_t keyblob[keyblob_num_words(config)];
  // Create blinded key.
  uint32_t hmac_key_mask[kPentestHmacMaxKeyWords];
  memset(hmac_key_mask, 0, HMAC_CMD_MAX_KEY_BYTES);
  for (size_t it = 0; it < kPentestHmacMaxKeyWords; it++) {
    hmac_key_mask[it] = pentest_ibex_rnd32_read();
  }
  HARDENED_TRY(
      keyblob_from_key_and_mask(key_buf, hmac_key_mask, config, keyblob));
  otcrypto_blinded_key_t hmac_key = {
      .config = config,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  hmac_key.checksum = integrity_blinded_checksum(&hmac_key);

  // Create input message.
  uint8_t msg_buf[data_in_len];
  memcpy(msg_buf, data_in, data_in_len);
  otcrypto_const_byte_buf_t input_message = {
      .len = data_in_len,
      .data = msg_buf,
  };

  // Create tag.
  uint32_t tag_buf[kPentestHmacMaxTagWords];
  otcrypto_word32_buf_t tag = {
      .len = tag_bytes / sizeof(uint32_t),
      .data = tag_buf,
  };

  // Trigger window.
  pentest_set_trigger_high();
  HARDENED_TRY(otcrypto_hmac(&hmac_key, input_message, tag));
  pentest_set_trigger_low();

  // Return data back to host.
  *data_out_len = tag_bytes;
  *cfg_out = 0;
  memset(data_out, 0, HMAC_CMD_MAX_TAG_BYTES);
  memcpy(data_out, tag_buf, tag_bytes);

  return OK_STATUS();
}
