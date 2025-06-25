// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/sca/cryptolib_sca_asym_impl.h"

#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/rsa.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/tests/penetrationtests/firmware/lib/cryptolib_asym.h"
#include "sw/device/tests/penetrationtests/firmware/lib/pentest_lib.h"
#include "sw/device/tests/penetrationtests/json/cryptolib_sca_asym_commands.h"

// OAEP label for testing.
static const unsigned char kTestLabel[] = "Test label.";
static const size_t kTestLabelLen = sizeof(kTestLabel) - 1;

status_t cryptolib_sca_rsa_dec_impl(
    uint8_t data[RSA_CMD_MAX_MESSAGE_BYTES], size_t data_len, size_t mode,
    uint32_t e, uint8_t n[RSA_CMD_MAX_N_BYTES], uint8_t d[RSA_CMD_MAX_N_BYTES],
    size_t *n_len, uint8_t data_out[RSA_CMD_MAX_MESSAGE_BYTES],
    size_t *data_out_len, size_t hashing, size_t padding, size_t cfg_in,
    size_t *cfg_out, size_t trigger) {
  size_t private_key_bytes;
  size_t private_key_blob_bytes;
  size_t num_words;
  size_t num_bytes;
  otcrypto_rsa_size_t rsa_size;
  switch (mode) {
    case kPentestRsa2048:
      private_key_bytes = kOtcryptoRsa2048PrivateKeyBytes;
      private_key_blob_bytes = kOtcryptoRsa2048PrivateKeyblobBytes;
      num_words = kPentestRsa2048NumWords;
      num_bytes = kPentestRsa2048NumBytes;
      rsa_size = kOtcryptoRsaSize2048;
      break;
    case kPentestRsa3072:
      private_key_bytes = kOtcryptoRsa3072PrivateKeyBytes;
      private_key_blob_bytes = kOtcryptoRsa3072PrivateKeyblobBytes;
      num_words = kPentestRsa3072NumWords;
      num_bytes = kPentestRsa3072NumBytes;
      rsa_size = kOtcryptoRsaSize3072;
      break;
    case kPentestRsa4096:
      private_key_bytes = kOtcryptoRsa4096PrivateKeyBytes;
      private_key_blob_bytes = kOtcryptoRsa4096PrivateKeyblobBytes;
      num_words = kPentestRsa4096NumWords;
      num_bytes = kPentestRsa4096NumBytes;
      rsa_size = kOtcryptoRsaSize4096;
      break;
    default:
      LOG_ERROR("Unsupported RSA mode: %d", mode);
      return INVALID_ARGUMENT();
  }

  // Sanity check inputs.
  TRY_CHECK(num_bytes == *n_len);
  // Ciphertext size is expected to be num_bytes.
  TRY_CHECK(num_bytes == data_len);

  otcrypto_hash_mode_t hash_mode;
  switch (hashing) {
    case kPentestRsaHashmodeSha256:
      hash_mode = kOtcryptoHashModeSha256;
      break;
    case kPentestRsaHashmodeSha384:
      hash_mode = kOtcryptoHashModeSha384;
      break;
    case kPentestRsaHashmodeSha512:
      hash_mode = kOtcryptoHashModeSha512;
      break;
    default:
      LOG_ERROR("Unsupported RSA hash mode: %d", hashing);
      return INVALID_ARGUMENT();
  }

  if (padding != 0) {
    LOG_ERROR("Only padding = 0 (OAEP) is supported.");
    return INVALID_ARGUMENT();
  }

  // Create two shares for the private exponent (second share is all-zero).
  uint32_t d_buf[kPentestRsaMaxDWords];
  memset(d_buf, 0, sizeof(d_buf));
  memcpy(d_buf, d, num_bytes);

  otcrypto_const_word32_buf_t d_share0 = {
      .data = d_buf,
      .len = num_words,
  };
  uint32_t share1[kPentestRsaMaxDWords] = {0};
  otcrypto_const_word32_buf_t d_share1 = {
      .data = share1,
      .len = num_words,
  };

  // Construct the private key.
  otcrypto_key_config_t private_key_config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeRsaEncryptOaep,
      .key_length = private_key_bytes,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  size_t keyblob_words = ceil_div(private_key_blob_bytes, sizeof(uint32_t));
  uint32_t keyblob[keyblob_words];
  otcrypto_blinded_key_t private_key = {
      .config = private_key_config,
      .keyblob = keyblob,
      .keyblob_length = private_key_blob_bytes,
  };

  // Create the modulus N buffer.
  uint32_t n_buf[kPentestRsaMaxNWords];
  memset(n_buf, 0, sizeof(d_buf));
  memcpy(n_buf, n, num_bytes);

  otcrypto_const_word32_buf_t modulus = {
      .data = n_buf,
      .len = num_words,
  };

  // Trigger window.
  if (trigger == 0) {
    pentest_set_trigger_high();
  }
  TRY(otcrypto_rsa_private_key_from_exponents(rsa_size, modulus, e, d_share0,
                                              d_share1, &private_key));
  if (trigger == 0) {
    pentest_set_trigger_low();
  }

  uint32_t ciphertext_buf[num_words];
  memset(ciphertext_buf, 0, sizeof(ciphertext_buf));
  memcpy(ciphertext_buf, data, data_len);

  otcrypto_const_word32_buf_t ciphertext = {
      .len = num_words,
      .data = ciphertext_buf,
  };

  // Create label.
  otcrypto_const_byte_buf_t label_buf = {.data = kTestLabel,
                                         .len = kTestLabelLen};

  // Create output buffer for the plaintext.
  uint8_t plaintext_buf[RSA_CMD_MAX_MESSAGE_BYTES];
  otcrypto_byte_buf_t plaintext = {
      .data = plaintext_buf,
      .len = num_words,
  };

  size_t msg_len;
  // Trigger window.
  if (trigger == 1) {
    pentest_set_trigger_high();
  }
  TRY(otcrypto_rsa_decrypt(&private_key, hash_mode, ciphertext, label_buf,
                           plaintext, &msg_len));
  if (trigger == 1) {
    pentest_set_trigger_low();
  }

  // Return data back to host.
  *data_out_len = msg_len;
  *cfg_out = 0;
  memset(data_out, 0, RSA_CMD_MAX_MESSAGE_BYTES);
  memcpy(data_out, plaintext_buf, msg_len);

  return OK_STATUS();
}
