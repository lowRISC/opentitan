// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/fi/cryptolib_fi_asym_impl.h"

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
#include "sw/device/tests/penetrationtests/json/cryptolib_fi_asym_commands.h"

// OAEP label for testing.
static const unsigned char kTestLabel[] = "Test label.";
static const size_t kTestLabelLen = sizeof(kTestLabel) - 1;

status_t cryptolib_fi_rsa_enc_impl(cryptolib_fi_asym_rsa_enc_in_t uj_input,
                                   cryptolib_fi_asym_rsa_enc_out_t *uj_output) {
  size_t public_key_bytes;
  size_t private_key_bytes;
  size_t private_key_blob_bytes;
  size_t num_words;
  size_t num_bytes;
  otcrypto_rsa_size_t rsa_size;
  switch (uj_input.mode) {
    case kPentestRsa2048:
      public_key_bytes = kOtcryptoRsa2048PublicKeyBytes;
      private_key_bytes = kOtcryptoRsa2048PrivateKeyBytes;
      private_key_blob_bytes = kOtcryptoRsa2048PrivateKeyblobBytes;
      num_words = kPentestRsa2048NumWords;
      num_bytes = kPentestRsa2048NumBytes;
      rsa_size = kOtcryptoRsaSize2048;
      break;
    case kPentestRsa3072:
      public_key_bytes = kOtcryptoRsa3072PublicKeyBytes;
      private_key_bytes = kOtcryptoRsa3072PrivateKeyBytes;
      private_key_blob_bytes = kOtcryptoRsa3072PrivateKeyblobBytes;
      num_words = kPentestRsa3072NumWords;
      num_bytes = kPentestRsa3072NumBytes;
      rsa_size = kOtcryptoRsaSize3072;
      break;
    case kPentestRsa4096:
      public_key_bytes = kOtcryptoRsa4096PublicKeyBytes;
      private_key_bytes = kOtcryptoRsa4096PrivateKeyBytes;
      private_key_blob_bytes = kOtcryptoRsa4096PrivateKeyblobBytes;
      num_words = kPentestRsa4096NumWords;
      num_bytes = kPentestRsa4096NumBytes;
      rsa_size = kOtcryptoRsaSize4096;
      break;
    default:
      LOG_ERROR("Unsupported RSA mode: %d", uj_input.mode);
      return INVALID_ARGUMENT();
  }

  // Sanity check inputs.
  TRY_CHECK(num_bytes == uj_input.n_len);

  otcrypto_hash_mode_t hash_mode;
  switch (uj_input.hashing) {
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
      LOG_ERROR("Unsupported RSA hash mode: %d", uj_input.hashing);
      return INVALID_ARGUMENT();
  }

  if (uj_input.padding != 0) {
    LOG_ERROR("Only padding = 0 (OAEP) is supported.");
    return INVALID_ARGUMENT();
  }

  // Create the modulus N buffer.
  uint32_t n_buf[kPentestRsaMaxNWords];
  memset(n_buf, 0, sizeof(n_buf));
  memcpy(n_buf, uj_input.n, num_bytes);

  otcrypto_const_word32_buf_t modulus = {
      .data = n_buf,
      .len = num_words,
  };

  // Create label.
  otcrypto_const_byte_buf_t label_buf = {.data = kTestLabel,
                                         .len = kTestLabelLen};

  if (uj_input.op_enc) {
    // Encryption.
    uint32_t public_key_data[ceil_div(public_key_bytes, sizeof(uint32_t))];

    // Construct the public key.
    otcrypto_unblinded_key_t public_key = {
        .key_mode = kOtcryptoKeyModeRsaEncryptOaep,
        .key_length = public_key_bytes,
        .key = public_key_data,
    };
    TRY(otcrypto_rsa_public_key_construct(rsa_size, modulus, uj_input.e,
                                          &public_key));

    // Create input message.
    uint8_t msg_buf[num_words];
    memcpy(msg_buf, uj_input.data, uj_input.data_len);
    otcrypto_const_byte_buf_t input_message = {
        .len = uj_input.data_len,
        .data = msg_buf,
    };

    // Output buffer.
    uint32_t ciphertext_buf[kPentestRsaMaxMsgWords];
    otcrypto_word32_buf_t ciphertext = {
        .data = ciphertext_buf,
        .len = num_words,
    };

    // Trigger window.
    if (uj_input.trigger == 0) {
      pentest_set_trigger_high();
    }
    TRY(otcrypto_rsa_encrypt(&public_key, hash_mode, input_message, label_buf,
                             ciphertext));
    if (uj_input.trigger == 0) {
      pentest_set_trigger_low();
    }

    // Return data back to host.
    uj_output->data_len = num_bytes;
    uj_output->cfg = 0;
    memset(uj_output->data, 0, RSA_CMD_MAX_MESSAGE_BYTES);
    memcpy(uj_output->data, ciphertext_buf, uj_output->data_len);
    // Return received n and d back to host.
    uj_output->n_len = uj_input.n_len;
    memset(uj_output->n, 0, RSA_CMD_MAX_N_BYTES);
    memcpy(uj_output->n, uj_input.n, uj_input.n_len);
    memset(uj_output->d, 0, RSA_CMD_MAX_N_BYTES);
    memcpy(uj_output->d, uj_input.d, uj_input.n_len);
  } else {
    // Decryption.

    // Create two shares for the private exponent (second share is all-zero).
    uint32_t d_buf[kPentestRsaMaxDWords];
    memset(d_buf, 0, sizeof(d_buf));
    memcpy(d_buf, uj_input.d, num_bytes);

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

    // Trigger window.
    if (uj_input.trigger == 0) {
      pentest_set_trigger_high();
    }
    TRY(otcrypto_rsa_private_key_from_exponents(
        rsa_size, modulus, uj_input.e, d_share0, d_share1, &private_key));
    if (uj_input.trigger == 0) {
      pentest_set_trigger_low();
    }

    uint32_t ciphertext_buf[num_words];
    memset(ciphertext_buf, 0, sizeof(ciphertext_buf));
    memcpy(ciphertext_buf, uj_input.data, uj_input.data_len);

    otcrypto_const_word32_buf_t ciphertext = {
        .len = num_words,
        .data = ciphertext_buf,
    };

    // Create output buffer for the plaintext.
    uint8_t plaintext_buf[RSA_CMD_MAX_MESSAGE_BYTES];
    otcrypto_byte_buf_t plaintext = {
        .data = plaintext_buf,
        .len = num_words,
    };

    size_t msg_len;
    // Trigger window.
    if (uj_input.trigger == 1) {
      pentest_set_trigger_high();
    }
    TRY(otcrypto_rsa_decrypt(&private_key, hash_mode, ciphertext, label_buf,
                             plaintext, &msg_len));
    if (uj_input.trigger == 1) {
      pentest_set_trigger_low();
    }

    // Return data back to host.
    uj_output->data_len = msg_len;
    uj_output->cfg = 0;
    memset(uj_output->data, 0, RSA_CMD_MAX_MESSAGE_BYTES);
    memcpy(uj_output->data, plaintext_buf, msg_len);
    // Return received n and d back to host.
    uj_output->n_len = uj_input.n_len;
    memset(uj_output->n, 0, RSA_CMD_MAX_N_BYTES);
    memcpy(uj_output->n, uj_input.n, uj_input.n_len);
    memset(uj_output->d, 0, RSA_CMD_MAX_N_BYTES);
    memcpy(uj_output->d, uj_input.d, uj_input.n_len);
  }

  return OK_STATUS();
}
