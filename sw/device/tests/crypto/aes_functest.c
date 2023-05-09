// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/aes.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/crypto/aes_testvectors.h"

// Random mask for testing.
static const uint32_t kKeyMask[8] = {
    0x1b81540c, 0x220733c9, 0x8bf85383, 0x05ab50b4,
    0x8acdcb7e, 0x15e76440, 0x8459b2ce, 0xdc2110cc,
};

static const size_t kAesBlockBytes = 128 / 8;

static crypto_key_config_t make_key_config(const aes_test_t *test) {
  key_mode_t key_mode;
  switch (test->mode) {
    case kBlockCipherModeEcb:
      LOG_INFO("Mode: ECB");
      key_mode = kKeyModeAesEcb;
      break;
    case kBlockCipherModeCbc:
      LOG_INFO("Mode: CBC");
      key_mode = kKeyModeAesCbc;
      break;
    case kBlockCipherModeCfb:
      LOG_INFO("Mode: CFB");
      key_mode = kKeyModeAesCfb;
      break;
    case kBlockCipherModeOfb:
      LOG_INFO("Mode: OFB");
      key_mode = kKeyModeAesOfb;
      break;
    case kBlockCipherModeCtr:
      LOG_INFO("Mode: CTR");
      key_mode = kKeyModeAesCtr;
      break;
    default:
      // Should be unreachable.
      CHECK(false, "Invalid block cipher mode.");
  };

  return (crypto_key_config_t){
      .version = kCryptoLibVersion1,
      .key_mode = key_mode,
      .key_length = test->key_len,
      .hw_backed = kHardenedBoolFalse,
      .diversification_hw_backed =
          (crypto_const_uint8_buf_t){.data = NULL, .len = 0},
      .security_level = kSecurityLevelLow,
  };
}

static void encrypt_decrypt_test(const aes_test_t *test) {
  // Determine the key configuration.
  crypto_key_config_t config = make_key_config(test);

  // Construct blinded key from the key and testing mask.
  uint32_t keyblob[keyblob_num_words(config)];
  CHECK_STATUS_OK(
      keyblob_from_key_and_mask(test->key, kKeyMask, config, keyblob));
  crypto_blinded_key_t key = {
      .config = config,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  key.checksum = integrity_blinded_checksum(&key);

  // Construct IV buffer.
  crypto_uint8_buf_t iv = {
      .data = (unsigned char *)test->iv,
      .len = kAesBlockBytes,
  };

  // Construct plaintext buffer.
  crypto_const_uint8_buf_t plaintext = {
      .data = (const unsigned char *)test->plaintext,
      .len = test->plaintext_len,
  };

  // Calculate the size of the padded plaintext.
  size_t padded_len_bytes;
  CHECK(otcrypto_aes_padded_plaintext_length(test->plaintext_len, test->padding,
                                             &padded_len_bytes) ==
        kCryptoStatusOK);
  CHECK(padded_len_bytes % sizeof(uint32_t) == 0);

  // Create buffer for ciphertext.
  uint32_t ciphertext_data[padded_len_bytes / sizeof(uint32_t)];
  crypto_uint8_buf_t ciphertext = {
      .data = (unsigned char *)ciphertext_data,
      .len = padded_len_bytes,
  };

  // Run encryption and check the result.
  CHECK(otcrypto_aes(&key, iv, test->mode, kAesOperationEncrypt, plaintext,
                     test->padding, ciphertext) == kCryptoStatusOK);

  CHECK_ARRAYS_EQ(ciphertext_data, test->exp_ciphertext,
                  ARRAYSIZE(ciphertext_data));

  // Create a const buffer for the ciphertext.
  crypto_const_uint8_buf_t const_ciphertext = {
      .data = (const unsigned char *)ciphertext_data,
      .len = padded_len_bytes,
  };

  // Construct a buffer for the recovered plaintext.
  uint32_t recovered_plaintext_data[ARRAYSIZE(ciphertext_data)];
  crypto_uint8_buf_t recovered_plaintext = {
      .data = (unsigned char *)recovered_plaintext_data,
      .len = padded_len_bytes,
  };

  // Run decryption and check the result (not including padding).
  CHECK(otcrypto_aes(&key, iv, test->mode, kAesOperationDecrypt,
                     const_ciphertext, test->padding,
                     recovered_plaintext) == kCryptoStatusOK);

  CHECK_ARRAYS_EQ((unsigned char *)recovered_plaintext_data,
                  (unsigned char *)test->plaintext, test->plaintext_len);
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  for (size_t i = 0; i < ARRAYSIZE(kAesTests); i++) {
    LOG_INFO("Starting AES test %d of %d...", i + 1, ARRAYSIZE(kAesTests));
    encrypt_decrypt_test(&kAesTests[i]);
    LOG_INFO("Finished AES test %d.", i + 1);
  }

  return true;
}
