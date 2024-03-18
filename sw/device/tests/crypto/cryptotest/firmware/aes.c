// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/aes.h"

#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/drivers/aes.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/crypto/cryptotest/json/aes_commands.h"
#include "sw/device/tests/crypto/cryptotest/json/aes_gcm_commands.h"

enum {
  kAesBlockBytes = 128 / 8,
  kAesBlockWords = kAesBlockBytes / sizeof(uint32_t),
  kAesMaxKeyBytes = 256 / 8,
  kAesMaxKeyWords = kAesMaxKeyBytes / 4,
  kStreamingAadChunkBytes = 10,
  kStreamingMessageChunkBytes = 20,
};

// Arbitrary mask for testing (borrowed from aes_functest.c).
static const uint32_t kKeyMask[8] = {
    0x1b81540c, 0x220733c9, 0x8bf85383, 0x05ab50b4,
    0x8acdcb7e, 0x15e76440, 0x8459b2ce, 0xdc2110cc,
};

/**
 * Stream an AES-GCM operation (encrypt or decrypt).
 *
 * The caller should call `otcrypto_aes_gcm_*_init()` before this operation and
 * `otcrypto_aes_gcm_*_final()` after.
 *
 * @param ctx AES-GCM context, modified in-place.
 * @param aad Associated data.
 * @param input Plaintext for encryption, or ciphertext for decryption.
 * @param[out] output Ciphertext for encryption, or plaintext for decryption.
 * @param[out] output_bytes_written Number of output bytes written.
 * @return OK or error.
 */
static status_t stream_gcm(otcrypto_aes_gcm_context_t *ctx,
                           otcrypto_const_byte_buf_t aad,
                           otcrypto_const_byte_buf_t input,
                           otcrypto_byte_buf_t output,
                           size_t *output_bytes_written) {
  // Stream the AAD. The last chunk may have a different length than the others.
  if (aad.len > 0) {
    size_t num_chunks = ceil_div(aad.len, kStreamingAadChunkBytes);
    for (size_t i = 0; i < num_chunks; i++) {
      size_t offset = i * kStreamingAadChunkBytes;
      size_t chunk_len = kStreamingAadChunkBytes;
      if (offset + chunk_len > aad.len) {
        chunk_len = aad.len - offset;
      }
      otcrypto_const_byte_buf_t aad_chunk = {
          .data = aad.data + offset,
          .len = chunk_len,
      };
      TRY(otcrypto_aes_gcm_update_aad(ctx, aad_chunk));
    }
  }

  // Stream the input, similary to the AAD except that this time we need to
  // accumulate incremental parts of the output.
  *output_bytes_written = 0;
  if (input.len > 0) {
    size_t num_chunks = ceil_div(input.len, kStreamingMessageChunkBytes);
    for (size_t i = 0; i < num_chunks; i++) {
      size_t offset = i * kStreamingMessageChunkBytes;
      size_t chunk_len = kStreamingMessageChunkBytes;
      if (offset + chunk_len > input.len) {
        chunk_len = input.len - offset;
      }
      otcrypto_const_byte_buf_t input_chunk = {
          .data = input.data + offset,
          .len = chunk_len,
      };
      otcrypto_byte_buf_t output_with_offset = {
          .data = output.data + *output_bytes_written,
          .len = output.len - *output_bytes_written,
      };
      size_t bytes_written_for_chunk = 0;
      TRY(otcrypto_aes_gcm_update_encrypted_data(
          ctx, input_chunk, output_with_offset, &bytes_written_for_chunk));
      *output_bytes_written += bytes_written_for_chunk;
    }
  }
  return OTCRYPTO_OK;
}

/**
 * Get the enum value for a given tag length.
 */
static otcrypto_aes_gcm_tag_len_t get_tag_length(size_t tag_len_bytes) {
  switch (tag_len_bytes) {
    case (128 / 8):
      return kOtcryptoAesGcmTagLen128;
    case (96 / 8):
      return kOtcryptoAesGcmTagLen96;
    case (64 / 8):
      return kOtcryptoAesGcmTagLen64;
    case (32 / 8):
      return kOtcryptoAesGcmTagLen32;
    default:
      // Should not get here.
      LOG_ERROR("Invalid GCM tag length %d", tag_len_bytes);
  }
  return 0;
}

status_t handle_aes_gcm_encryption(ujson_t *uj,
                                   cryptotest_aes_gcm_data_t uj_data,
                                   otcrypto_blinded_key_t key,
                                   otcrypto_const_word32_buf_t iv,
                                   otcrypto_const_byte_buf_t aad) {
  // Text block length should be a multiple of `kAesBlockNumBytes`.
  size_t nblocks = ceil_div(uj_data.input_length, kAesBlockNumBytes);
  size_t text_buffer_length = nblocks * kAesBlockNumBytes;

  // Set the plaintext field
  otcrypto_const_byte_buf_t plaintext = {
      .data = uj_data.input,
      .len = text_buffer_length,
  };

  // Set the ciphertext field
  uint8_t ciphertext_data[text_buffer_length];
  otcrypto_byte_buf_t ciphertext = {
      .data = ciphertext_data,
      .len = text_buffer_length,
  };

  // Set the auth_tag and tag_len
  size_t tag_num_words = ceil_div(uj_data.tag_length, sizeof(uint32_t));
  uint32_t tag_buf[tag_num_words];
  memcpy(tag_buf, uj_data.tag, uj_data.tag_length);
  otcrypto_word32_buf_t auth_tag = {
      .data = tag_buf,
      .len = tag_num_words,
  };
  otcrypto_aes_gcm_tag_len_t tag_len =
      get_tag_length(tag_num_words * sizeof(uint32_t));
  if (tag_len == 0) {
    return INVALID_ARGUMENT();
  }

  // Test oneshot API
  otcrypto_status_t status = otcrypto_aes_gcm_encrypt(
      &key, plaintext, iv, aad, tag_len, ciphertext, auth_tag);

  if (status.value != kOtcryptoStatusValueOk) {
    return INTERNAL(status.value);
  }

  // Copy oneshot output to uJSON typer
  cryptotest_aes_gcm_output_t uj_output;
  uj_output.output_length = uj_data.input_length;
  memcpy(uj_output.oneshot_output, ciphertext.data, uj_output.output_length);

  // Test stepwise API
  otcrypto_aes_gcm_context_t ctx;
  status = otcrypto_aes_gcm_encrypt_init(&key, iv, &ctx);
  if (status.value != kOtcryptoStatusValueOk) {
    return INTERNAL(status.value);
  }

  size_t ciphertext_bytes_written;
  TRY(stream_gcm(&ctx, aad, plaintext, ciphertext, &ciphertext_bytes_written));
  otcrypto_byte_buf_t remaining_ciphertext = {
      .data = ciphertext.data + ciphertext_bytes_written,
      .len = uj_data.input_length - ciphertext_bytes_written,
  };
  TRY(otcrypto_aes_gcm_encrypt_final(&ctx, tag_len, remaining_ciphertext,
                                     &ciphertext_bytes_written, auth_tag));
  memcpy(uj_output.stepwise_output, ciphertext.data, uj_output.output_length);

  // Send digest to host via UART
  RESP_OK(ujson_serialize_cryptotest_aes_gcm_output_t, uj, &uj_output);
  return OK_STATUS(0);
}

status_t handle_aes_gcm_decryption(ujson_t *uj,
                                   cryptotest_aes_gcm_data_t uj_data,
                                   otcrypto_blinded_key_t key,
                                   otcrypto_const_word32_buf_t iv,
                                   otcrypto_const_byte_buf_t aad,
                                   hardened_bool_t *success) {
  // Text block length should be a multiple of `kAesBlockNumBytes`.
  size_t nblocks = ceil_div(uj_data.input_length, kAesBlockNumBytes);
  size_t text_buffer_length = nblocks * kAesBlockNumBytes;

  // Set the ciphertext field
  otcrypto_const_byte_buf_t ciphertext = {
      .data = uj_data.input,
      .len = text_buffer_length,
  };

  // Set the plaintext field
  uint8_t plaintext_data[text_buffer_length];
  otcrypto_byte_buf_t plaintext = {
      .data = plaintext_data,
      .len = text_buffer_length,
  };

  // Set the auth_tag and tag_len
  size_t tag_num_words = ceil_div(uj_data.tag_length, sizeof(uint32_t));
  uint32_t tag_buf[tag_num_words];
  memcpy(tag_buf, uj_data.tag, uj_data.tag_length);
  otcrypto_const_word32_buf_t auth_tag = {
      .data = tag_buf,
      .len = tag_num_words,
  };
  otcrypto_aes_gcm_tag_len_t tag_len =
      get_tag_length(tag_num_words * sizeof(uint32_t));
  if (tag_len == 0) {
    return INVALID_ARGUMENT();
  }

  // Test oneshot API
  otcrypto_status_t status = otcrypto_aes_gcm_decrypt(
      &key, ciphertext, iv, aad, tag_len, auth_tag, plaintext, success);

  if (status.value != kOtcryptoStatusValueOk) {
    return INTERNAL(status.value);
  }

  // Copy oneshot output to uJSON typer
  cryptotest_aes_gcm_output_t uj_output;
  uj_output.output_length = uj_data.input_length;
  memcpy(uj_output.oneshot_output, plaintext.data, uj_output.output_length);

  // Test stepwise API
  otcrypto_aes_gcm_context_t ctx;
  status = otcrypto_aes_gcm_decrypt_init(&key, iv, &ctx);
  if (status.value != kOtcryptoStatusValueOk) {
    return INTERNAL(status.value);
  }

  size_t plaintext_bytes_written;
  TRY(stream_gcm(&ctx, aad, ciphertext, plaintext, &plaintext_bytes_written));
  otcrypto_byte_buf_t remaining_plaintext = {
      .data = plaintext.data + plaintext_bytes_written,
      .len = uj_data.input_length - plaintext_bytes_written,
  };
  TRY(otcrypto_aes_gcm_decrypt_final(&ctx, auth_tag, tag_len,
                                     remaining_plaintext,
                                     &plaintext_bytes_written, success));
  memcpy(uj_output.stepwise_output, plaintext.data, uj_output.output_length);

  // Send digest to host via UART
  RESP_OK(ujson_serialize_cryptotest_aes_gcm_output_t, uj, &uj_output);
  return OK_STATUS(0);
}

status_t handle_aes_gcm(ujson_t *uj) {
  // Declare test arguments
  cryptotest_aes_gcm_operation_t uj_op;
  cryptotest_aes_gcm_data_t uj_data;

  // Deserialize test arguments from UART
  TRY(ujson_deserialize_cryptotest_aes_gcm_operation_t(uj, &uj_op));
  TRY(ujson_deserialize_cryptotest_aes_gcm_data_t(uj, &uj_data));

  // Build the key configuration
  otcrypto_key_config_t config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeAesGcm,
      .key_length = uj_data.key_length,  // length in bytes
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };

  // Create 32-bit key buffer
  size_t key_num_words = ceil_div(uj_data.key_length, sizeof(uint32_t));
  uint32_t key_buf[key_num_words];
  memcpy(key_buf, uj_data.key, uj_data.key_length);

  // Construct blinded key from the key and testing mask.
  uint32_t keyblob[keyblob_num_words(config)];
  TRY(keyblob_from_key_and_mask(key_buf, kKeyMask, config, keyblob));

  // Construct key
  otcrypto_blinded_key_t key = {
      .config = config,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
      .checksum = 0,
  };

  // Set the checksum
  key.checksum = integrity_blinded_checksum(&key);

  // Set the IV data
  size_t iv_num_words = ceil_div(uj_data.iv_length, sizeof(uint32_t));
  uint32_t iv_buf[iv_num_words];
  memcpy(iv_buf, uj_data.iv, uj_data.iv_length);
  otcrypto_const_word32_buf_t iv = {
      .data = iv_buf,
      .len = iv_num_words,
  };

  // IV length must be 96 or 128 bits = 3 or 4 words.
  // We return a response with output length = 0 so that
  // the rust harness can catch the correct test status.
  if (iv_num_words != 3 && iv_num_words != 4) {
    cryptotest_aes_gcm_output_t uj_output;
    memset(&uj_output, 0, sizeof(uj_output));
    RESP_OK(ujson_serialize_cryptotest_aes_gcm_output_t, uj, &uj_output);
    return OK_STATUS(0);
  }

  // Set the AAD
  uint8_t aad_buf[uj_data.aad_length];
  memcpy(aad_buf, uj_data.aad, uj_data.aad_length);
  otcrypto_const_byte_buf_t aad = {
      .data = aad_buf,
      .len = uj_data.aad_length,
  };

  hardened_bool_t success;
  switch (uj_op) {
    case kCryptotestAesGcmOperationEncrypt:
      return handle_aes_gcm_encryption(uj, uj_data, key, iv, aad);
    case kCryptotestAesGcmOperationDecrypt:
      return handle_aes_gcm_decryption(uj, uj_data, key, iv, aad, &success);
    default:
      LOG_ERROR("Invalid operation type!");
      return INVALID_ARGUMENT();
  }
  // To avoid possible compiler warning
  return INVALID_ARGUMENT();
}

status_t handle_aes_block(ujson_t *uj) {
  cryptotest_aes_mode_t uj_mode;
  cryptotest_aes_operation_t uj_op;
  cryptotest_aes_padding_t uj_padding;
  cryptotest_aes_data_t uj_data;
  TRY(ujson_deserialize_cryptotest_aes_mode_t(uj, &uj_mode));
  TRY(ujson_deserialize_cryptotest_aes_operation_t(uj, &uj_op));
  TRY(ujson_deserialize_cryptotest_aes_padding_t(uj, &uj_padding));
  TRY(ujson_deserialize_cryptotest_aes_data_t(uj, &uj_data));

  otcrypto_aes_mode_t mode;
  otcrypto_key_mode_t key_mode;
  switch (uj_mode) {
    case kCryptotestAesModeEcb:
      mode = kOtcryptoAesModeEcb;
      key_mode = kOtcryptoKeyModeAesEcb;
      break;
    case kCryptotestAesModeCbc:
      mode = kOtcryptoAesModeCbc;
      key_mode = kOtcryptoKeyModeAesCbc;
      break;
    case kCryptotestAesModeCfb:
      mode = kOtcryptoAesModeCfb;
      key_mode = kOtcryptoKeyModeAesCfb;
      break;
    case kCryptotestAesModeOfb:
      mode = kOtcryptoAesModeOfb;
      key_mode = kOtcryptoKeyModeAesOfb;
      break;
    case kCryptotestAesModeCtr:
      mode = kOtcryptoAesModeCtr;
      key_mode = kOtcryptoKeyModeAesCtr;
      break;
    default:
      LOG_ERROR("Unrecognized AES block cipher mode: %d", uj_mode);
      return INVALID_ARGUMENT();
  }

  otcrypto_aes_operation_t op;
  switch (uj_op) {
    case kCryptotestAesOperationEncrypt:
      op = kOtcryptoAesOperationEncrypt;
      break;
    case kCryptotestAesOperationDecrypt:
      op = kOtcryptoAesOperationDecrypt;
      break;
    default:
      LOG_ERROR("Unrecognized AES operation: %d", uj_op);
      return INVALID_ARGUMENT();
  }

  otcrypto_aes_padding_t padding;
  switch (uj_padding) {
    case kCryptotestAesPaddingPkcs7:
      padding = kOtcryptoAesPaddingPkcs7;
      break;
    case kCryptotestAesPaddingIso9797M2:
      padding = kOtcryptoAesPaddingIso9797M2;
      break;
    case kCryptotestAesPaddingNull:
      padding = kOtcryptoAesPaddingNull;
      break;
    default:
      LOG_ERROR("Unrecognized AES padding scheme: %d", uj_op);
      return INVALID_ARGUMENT();
  }

  // Convert the data struct into cryptolib types
  const size_t AES_IV_SIZE = 4;
  uint32_t iv_buf[AES_IV_SIZE];
  memcpy(iv_buf, uj_data.iv, AES_IV_SIZE * 4);
  otcrypto_word32_buf_t iv = {
      .data = iv_buf,
      .len = kAesBlockWords,
  };

  otcrypto_const_byte_buf_t input = {
      .data = uj_data.input,
      .len = (size_t)uj_data.input_len,
  };

  // Build the key configuration
  otcrypto_key_config_t config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = key_mode,
      .key_length = uj_data.key_length,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
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

  size_t padded_len_bytes;
  otcrypto_aes_padded_plaintext_length((size_t)uj_data.input_len, padding,
                                       &padded_len_bytes);
  if (padded_len_bytes > AES_CMD_MAX_MSG_BYTES) {
    return OUT_OF_RANGE();
  }
  uint32_t output_buf[padded_len_bytes / sizeof(uint32_t)];
  otcrypto_byte_buf_t output = {
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
