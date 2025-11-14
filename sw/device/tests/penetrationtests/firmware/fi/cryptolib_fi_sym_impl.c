// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/fi/cryptolib_fi_sym_impl.h"

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
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/tests/penetrationtests/firmware/lib/cryptolib_sym.h"
#include "sw/device/tests/penetrationtests/firmware/lib/pentest_lib.h"
#include "sw/device/tests/penetrationtests/json/cryptolib_fi_sym_commands.h"

#define MODULE_ID MAKE_MODULE_ID('c', 'f', 's')

// Markers in the dis file to be able to trace certain functions
#define PENTEST_MARKER_LABEL(name) asm volatile(#name ":" ::: "memory")

status_t cryptolib_fi_aes_impl(cryptolib_fi_sym_aes_in_t uj_input,
                               cryptolib_fi_sym_aes_out_t *uj_output) {
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
      .security_level = kOtcryptoKeySecurityLevelHigh,
  };

  // Create buffer to store key.
  uint32_t key_buf[kPentestAesMaxKeyWords];
  memset(key_buf, 0, AES_CMD_MAX_KEY_BYTES);
  memcpy(key_buf, uj_input.key, uj_input.key_len);
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
  PENTEST_MARKER_LABEL(PENTEST_MARKER_AES_START);
  pentest_set_trigger_high();
  HARDENED_TRY(otcrypto_aes(&key, iv, mode, op, input, padding, output));
  pentest_set_trigger_low();
  PENTEST_MARKER_LABEL(PENTEST_MARKER_AES_END);

  // Return data back to host.
  uj_output->data_len = padded_len_bytes;
  uj_output->cfg = 0;
  memset(uj_output->data, 0, AES_CMD_MAX_MSG_BYTES);
  memcpy(uj_output->data, output_buf, uj_output->data_len);

  return OK_STATUS();
}

status_t cryptolib_fi_drbg_generate_impl(
    cryptolib_fi_sym_drbg_generate_in_t uj_input,
    cryptolib_fi_sym_drbg_generate_out_t *uj_output) {
  // Nonce buffer used for the generate command of the DRBG.
  uint8_t nonce_buf[uj_input.nonce_len];
  memcpy(nonce_buf, uj_input.nonce, uj_input.nonce_len);

  otcrypto_const_byte_buf_t nonce = {
      .len = uj_input.nonce_len,
      .data = nonce_buf,
  };

  // Buffer for the output entropy data.
  uint32_t output_data[uj_input.data_len];
  otcrypto_word32_buf_t output = {
      .data = output_data,
      .len = ARRAYSIZE(output_data),
  };

  // Trigger window 0.
  if (uj_input.trigger & kPentestTrigger2) {
    PENTEST_MARKER_LABEL(PENTEST_MARKER_DRBG_GENERATE_START);
    pentest_set_trigger_high();
  }
  HARDENED_TRY(otcrypto_drbg_generate(nonce, output));
  if (uj_input.trigger & kPentestTrigger2) {
    pentest_set_trigger_low();
    PENTEST_MARKER_LABEL(PENTEST_MARKER_DRBG_GENERATE_END);
  }

  // Return data back to host.
  uj_output->cfg = 0;
  memset(uj_output->data, 0, DRBG_CMD_MAX_OUTPUT_BYTES);
  memcpy(uj_output->data, output_data, uj_input.data_len);

  return OK_STATUS();
}

status_t cryptolib_fi_drbg_reseed_impl(
    cryptolib_fi_sym_drbg_reseed_in_t uj_input,
    cryptolib_fi_sym_drbg_reseed_out_t *uj_output) {
  // Entropy buffer used for the instantiation of the DRBG.
  uint8_t entropy_buf[uj_input.entropy_len];
  memcpy(entropy_buf, uj_input.entropy, uj_input.entropy_len);

  otcrypto_const_byte_buf_t entropy = {
      .len = uj_input.entropy_len,
      .data = entropy_buf,
  };

  // Trigger window 0.
  if (uj_input.trigger & kPentestTrigger1) {
    PENTEST_MARKER_LABEL(PENTEST_MARKER_DRBG_RESEED_START);
    pentest_set_trigger_high();
  }
  HARDENED_TRY(otcrypto_drbg_instantiate(entropy));
  if (uj_input.trigger & kPentestTrigger1) {
    pentest_set_trigger_low();
    PENTEST_MARKER_LABEL(PENTEST_MARKER_DRBG_RESEED_END);
  }

  // Return data back to host.
  uj_output->cfg = 0;

  return OK_STATUS();
}

status_t cryptolib_fi_gcm_impl(cryptolib_fi_sym_gcm_in_t uj_input,
                               cryptolib_fi_sym_gcm_out_t *uj_output) {
  // Construct the blinded key configuration.
  otcrypto_key_config_t config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeAesGcm,
      .key_length = uj_input.key_len,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelHigh,
  };

  // Construct blinded key from the key and testing mask.
  uint32_t key_buf[kPentestAesMaxKeyWords];
  memset(key_buf, 0, AES_CMD_MAX_KEY_BYTES);
  memcpy(key_buf, uj_input.key, uj_input.key_len);

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
  otcrypto_blinded_key_t key = {
      .config = config,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
      .checksum = 0,
  };

  // Set the checksum.
  key.checksum = integrity_blinded_checksum(&key);

  // Prepare the input buffers.
  size_t iv_num_words = 4;
  uint32_t iv_data[iv_num_words];
  memcpy(iv_data, uj_input.iv, sizeof(iv_data));
  otcrypto_const_word32_buf_t iv = {
      .data = iv_data,
      .len = iv_num_words,
  };
  otcrypto_const_byte_buf_t plaintext = {
      .data = uj_input.data,
      .len = uj_input.data_len,
  };
  otcrypto_const_byte_buf_t aad = {
      .data = uj_input.aad,
      .len = uj_input.aad_len,
  };

  size_t tag_num_words =
      (uj_input.tag_len + sizeof(uint32_t) - 1) / sizeof(uint32_t);
  uint32_t actual_tag_data[tag_num_words];
  otcrypto_word32_buf_t actual_tag = {
      .data = actual_tag_data,
      .len = tag_num_words,
  };

  uint8_t actual_ciphertext_data[AES_CMD_MAX_MSG_BYTES];
  otcrypto_byte_buf_t actual_ciphertext = {
      .data = actual_ciphertext_data,
      .len = uj_input.data_len,
  };

  otcrypto_aes_gcm_tag_len_t tag_len;
  switch (uj_input.tag_len) {
    case (128 / 8):
      tag_len = kOtcryptoAesGcmTagLen128;
      break;
    case (96 / 8):
      tag_len = kOtcryptoAesGcmTagLen96;
      break;
    case (64 / 8):
      tag_len = kOtcryptoAesGcmTagLen64;
      break;
    case (32 / 8):
      tag_len = kOtcryptoAesGcmTagLen32;
      break;
    default:
      LOG_ERROR("Unrecognized AES-GCM tag length: %d", uj_input.tag_len);
      return INVALID_ARGUMENT();
  }

  // Trigger window.
  PENTEST_MARKER_LABEL(PENTEST_MARKER_GCM_ENCRYPT_START);
  pentest_set_trigger_high();
  HARDENED_TRY(otcrypto_aes_gcm_encrypt(&key, plaintext, iv, aad, tag_len,
                                        actual_ciphertext, actual_tag));
  pentest_set_trigger_low();
  PENTEST_MARKER_LABEL(PENTEST_MARKER_GCM_ENCRYPT_END);

  // Return data back to host.
  uj_output->cfg = 0;
  // Ciphertext.
  uj_output->data_len = uj_input.data_len;
  memset(uj_output->data, 0, AES_CMD_MAX_MSG_BYTES);
  memcpy(uj_output->data, actual_ciphertext_data, uj_output->data_len);
  // Tag.
  uj_output->tag_len = uj_input.tag_len;
  memset(uj_output->tag, 0, AES_CMD_MAX_MSG_BYTES);
  memcpy(uj_output->tag, actual_tag_data, uj_output->tag_len);

  return OK_STATUS();
}

status_t cryptolib_fi_hmac_impl(cryptolib_fi_sym_hmac_in_t uj_input,
                                cryptolib_fi_sym_hmac_out_t *uj_output) {
  // Set the HMAC mode.
  otcrypto_key_mode_t key_mode;
  unsigned int tag_bytes;
  switch (uj_input.mode) {
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
      LOG_ERROR("Unsupported HMAC key mode: %d", uj_input.mode);
      return INVALID_ARGUMENT();
  }

  // Build the key configuration.
  otcrypto_key_config_t config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = key_mode,
      .key_length = uj_input.key_len,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelHigh,
  };

  // Create buffer to store key.
  uint32_t key_buf[kPentestHmacMaxKeyWords];
  memset(key_buf, 0, HMAC_CMD_MAX_KEY_BYTES);
  memcpy(key_buf, uj_input.key, uj_input.key_len);
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
  otcrypto_blinded_key_t key = {
      .config = config,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  key.checksum = integrity_blinded_checksum(&key);

  // Create input message.
  uint8_t msg_buf[uj_input.data_len];
  memcpy(msg_buf, uj_input.data, uj_input.data_len);
  otcrypto_const_byte_buf_t input_message = {
      .len = uj_input.data_len,
      .data = msg_buf,
  };

  // Create tag.
  uint32_t tag_buf[kPentestHmacMaxTagWords];
  otcrypto_word32_buf_t tag = {
      .len = tag_bytes / sizeof(uint32_t),
      .data = tag_buf,
  };

  // Trigger window.
  PENTEST_MARKER_LABEL(PENTEST_MARKER_HMAC_START);
  pentest_set_trigger_high();
  HARDENED_TRY(otcrypto_hmac(&key, input_message, tag));
  pentest_set_trigger_low();
  PENTEST_MARKER_LABEL(PENTEST_MARKER_HMAC_END);

  // Return data back to host.
  uj_output->data_len = tag_bytes;
  uj_output->cfg = 0;
  memset(uj_output->data, 0, HMAC_CMD_MAX_TAG_BYTES);
  memcpy(uj_output->data, tag_buf, uj_output->data_len);

  return OK_STATUS();
}
