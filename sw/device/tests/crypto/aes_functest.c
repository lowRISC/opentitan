// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/aes.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/entropy_src.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/crypto/aes_testvectors.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

// Random mask for testing.
static const uint32_t kKeyMask[8] = {
    0x1b81540c, 0x220733c9, 0x8bf85383, 0x05ab50b4,
    0x8acdcb7e, 0x15e76440, 0x8459b2ce, 0xdc2110cc,
};

// Global pointer to the current test.
static const aes_test_t *test = NULL;

enum {
  kAesBlockBytes = 128 / 8,
  kAesBlockWords = kAesBlockBytes / sizeof(uint32_t),
};

static otcrypto_key_config_t make_key_config(const aes_test_t *test) {
  otcrypto_key_mode_t key_mode;
  switch (test->mode) {
    case kOtcryptoAesModeEcb:
      LOG_INFO("Mode: ECB");
      key_mode = kOtcryptoKeyModeAesEcb;
      break;
    case kOtcryptoAesModeCbc:
      LOG_INFO("Mode: CBC");
      key_mode = kOtcryptoKeyModeAesCbc;
      break;
    case kOtcryptoAesModeCfb:
      LOG_INFO("Mode: CFB");
      key_mode = kOtcryptoKeyModeAesCfb;
      break;
    case kOtcryptoAesModeOfb:
      LOG_INFO("Mode: OFB");
      key_mode = kOtcryptoKeyModeAesOfb;
      break;
    case kOtcryptoAesModeCtr:
      LOG_INFO("Mode: CTR");
      key_mode = kOtcryptoKeyModeAesCtr;
      break;
    default:
      // Should be unreachable.
      CHECK(false, "Invalid block cipher mode.");
  };

  return (otcrypto_key_config_t){
      .version = kOtcryptoLibVersion1,
      .key_mode = key_mode,
      .key_length = test->key_len,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
}

/**
 * Run AES encryption for the given test vector.
 *
 * If `streaming` is true, we will process the plaintext in small chunks to
 * ensure that the IV is updating correctly.
 *
 * @param test Test vector to run.
 * @param streaming Whether to run in streaming mode.
 */
static status_t run_encrypt(const aes_test_t *test, bool streaming) {
  // Determine the key configuration.
  otcrypto_key_config_t config = make_key_config(test);

  // Construct blinded key from the key and testing mask.
  uint32_t keyblob[keyblob_num_words(config)];
  TRY(keyblob_from_key_and_mask(test->key, kKeyMask, config, keyblob));
  otcrypto_blinded_key_t key = {
      .config = config,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  key.checksum = integrity_blinded_checksum(&key);

  // Construct a buffer to hold the IV.
  uint32_t iv_data[kAesBlockWords];
  memcpy(iv_data, test->iv, kAesBlockBytes);
  otcrypto_word32_buf_t iv =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, iv_data, kAesBlockWords);

  // Calculate the size of the padded plaintext.
  size_t padded_len_bytes;
  TRY(otcrypto_aes_padded_plaintext_length(test->plaintext_len, test->padding,
                                           &padded_len_bytes));

  // Create buffer for ciphertext.
  uint32_t ciphertext_data[padded_len_bytes / sizeof(uint32_t)];

  // If in streaming mode, encrypt one block at a time with null padding until
  // there is at most 1 block of input remaining.
  size_t plaintext_len = test->plaintext_len;
  size_t ciphertext_len = sizeof(ciphertext_data);
  const unsigned char *plaintext = (const unsigned char *)test->plaintext;
  unsigned char *ciphertext = (unsigned char *)ciphertext_data;
  if (streaming) {
    while (plaintext_len > kAesBlockBytes) {
      otcrypto_const_byte_buf_t plaintext_block = OTCRYPTO_MAKE_BUF(
          otcrypto_const_byte_buf_t, plaintext, kAesBlockBytes);
      otcrypto_byte_buf_t ciphertext_block =
          OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, ciphertext, kAesBlockBytes);
      TRY(otcrypto_aes(&key, &iv, test->mode, kOtcryptoAesOperationEncrypt,
                       &plaintext_block, kOtcryptoAesPaddingNull,
                       &ciphertext_block));
      plaintext += kAesBlockBytes;
      ciphertext += kAesBlockBytes;
      plaintext_len -= kAesBlockBytes;
      ciphertext_len -= kAesBlockBytes;
    }
  }

  // Encrypt the remaining input in one shot with the requested padding.
  otcrypto_const_byte_buf_t plaintext_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, plaintext, plaintext_len);
  otcrypto_byte_buf_t ciphertext_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, ciphertext, ciphertext_len);
  TRY(otcrypto_aes(&key, &iv, test->mode, kOtcryptoAesOperationEncrypt,
                   &plaintext_buf, test->padding, &ciphertext_buf));

  TRY_CHECK_ARRAYS_EQ(ciphertext_data, test->exp_ciphertext,
                      ARRAYSIZE(ciphertext_data));
  return OK_STATUS();
}

/**
 * Run AES decryption for the given test vector.
 *
 * If `streaming` is true, we will process the ciphertext in small chunks to
 * ensure that the IV is updating correctly.
 *
 * @param test Test vector to run.
 * @param streaming Whether to run in streaming mode.
 */
static status_t run_decrypt(const aes_test_t *test, bool streaming) {
  // Determine the key configuration.
  otcrypto_key_config_t config = make_key_config(test);

  // Construct blinded key from the key and testing mask.
  uint32_t keyblob[keyblob_num_words(config)];
  TRY(keyblob_from_key_and_mask(test->key, kKeyMask, config, keyblob));
  otcrypto_blinded_key_t key = {
      .config = config,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  key.checksum = integrity_blinded_checksum(&key);

  // Construct a buffer to hold the IV.
  uint32_t iv_data[kAesBlockWords];
  memcpy(iv_data, test->iv, kAesBlockBytes);
  otcrypto_word32_buf_t iv =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, iv_data, kAesBlockWords);

  // Calculate the size of the padded plaintext.
  size_t padded_len_bytes;
  TRY(otcrypto_aes_padded_plaintext_length(test->plaintext_len, test->padding,
                                           &padded_len_bytes));

  // Construct a buffer for the recovered plaintext.
  TRY_CHECK(padded_len_bytes % sizeof(uint32_t) == 0);
  size_t padded_len_words = padded_len_bytes / sizeof(uint32_t);
  uint32_t recovered_plaintext_data[padded_len_words];
  memset(recovered_plaintext_data, 0, sizeof(recovered_plaintext_data));

  // If in streaming mode, decrypt one block at a time with null padding until
  // there is only 1 block of input remaining.
  size_t len = sizeof(recovered_plaintext_data);
  const unsigned char *ciphertext = (const unsigned char *)test->exp_ciphertext;
  unsigned char *recovered_plaintext =
      (unsigned char *)recovered_plaintext_data;
  if (streaming) {
    while (len > kAesBlockBytes) {
      otcrypto_const_byte_buf_t ciphertext_block = OTCRYPTO_MAKE_BUF(
          otcrypto_const_byte_buf_t, ciphertext, kAesBlockBytes);
      otcrypto_byte_buf_t recovered_plaintext_block = OTCRYPTO_MAKE_BUF(
          otcrypto_byte_buf_t, recovered_plaintext, kAesBlockBytes);
      TRY(otcrypto_aes(&key, &iv, test->mode, kOtcryptoAesOperationDecrypt,
                       &ciphertext_block, kOtcryptoAesPaddingNull,
                       &recovered_plaintext_block));
      ciphertext += kAesBlockBytes;
      recovered_plaintext += kAesBlockBytes;
      len -= kAesBlockBytes;
    }
    // Expect that the length is now exactly one block, since the ciphertext
    // length should be a multiple of the block size.
    TRY_CHECK(len == kAesBlockBytes);
  }

  // Decrypt the remaining input in one shot.
  otcrypto_const_byte_buf_t ciphertext_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, ciphertext, len);
  otcrypto_byte_buf_t recovered_plaintext_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, recovered_plaintext, len);
  TRY(otcrypto_aes(&key, &iv, test->mode, kOtcryptoAesOperationDecrypt,
                   &ciphertext_buf, test->padding, &recovered_plaintext_buf));

  // Check the result (not including padding).
  TRY_CHECK_ARRAYS_EQ((unsigned char *)recovered_plaintext_data,
                      (unsigned char *)test->plaintext, test->plaintext_len);

  return OK_STATUS();
}

/**
 * Test one-shot AES encryption.
 */
static status_t encrypt_test(void) {
  return run_encrypt(test, /*streaming=*/false);
}

/**
 * Test one-shot AES decryption.
 */
static status_t decrypt_test(void) {
  return run_decrypt(test, /*streaming=*/false);
}

/**
 * Test streaming AES encryption.
 */
static status_t encrypt_streaming_test(void) {
  return run_encrypt(test, /*streaming=*/true);
}

/**
 * Test streaming AES decryption.
 */
static status_t decrypt_streaming_test(void) {
  return run_decrypt(test, /*streaming=*/true);
}

/**
 * Negative tests.
 */
static status_t run_negative_tests(void) {
  LOG_INFO("Running negative tests for AES API...");

  otcrypto_key_config_t config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeAesCbc,
      .key_length = 16,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };

  uint32_t keyblob[8] = {0};
  otcrypto_blinded_key_t key = {
      .config = config,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  key.checksum = integrity_blinded_checksum(&key);

  uint32_t iv_data[kAesBlockWords] = {0};
  otcrypto_word32_buf_t iv =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, iv_data, kAesBlockWords);

  uint8_t input_data[16] = {0};
  otcrypto_const_byte_buf_t input = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, input_data, sizeof(input_data));

  uint8_t output_data[32] = {0};
  otcrypto_byte_buf_t output =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, output_data, 16);

  // Test NULL pointers
  CHECK(otcrypto_aes(NULL, &iv, kOtcryptoAesModeCbc,
                     kOtcryptoAesOperationEncrypt, &input,
                     kOtcryptoAesPaddingNull, &output)
            .value == OTCRYPTO_BAD_ARGS.value);
  otcrypto_word32_buf_t bad_iv =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, NULL, kAesBlockWords);
  CHECK(otcrypto_aes(&key, &bad_iv, kOtcryptoAesModeCbc,
                     kOtcryptoAesOperationEncrypt, &input,
                     kOtcryptoAesPaddingNull, &output)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Test decryption with invalid length
  otcrypto_const_byte_buf_t bad_len_input =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, input_data, 15);
  CHECK(otcrypto_aes(&key, &iv, kOtcryptoAesModeCbc,
                     kOtcryptoAesOperationDecrypt, &bad_len_input,
                     kOtcryptoAesPaddingNull, &output)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Test null padding with an unaligned input length
  CHECK(otcrypto_aes(&key, &iv, kOtcryptoAesModeCbc,
                     kOtcryptoAesOperationEncrypt, &bad_len_input,
                     kOtcryptoAesPaddingNull, &output)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Test output buffer length mismatch
  otcrypto_byte_buf_t bad_len_output =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, output_data, 32);
  CHECK(otcrypto_aes(&key, &iv, kOtcryptoAesModeCbc,
                     kOtcryptoAesOperationEncrypt, &input,
                     kOtcryptoAesPaddingNull, &bad_len_output)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Test invalid IV length
  otcrypto_word32_buf_t bad_len_iv =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, iv_data, 3);
  CHECK(otcrypto_aes(&key, &bad_len_iv, kOtcryptoAesModeCbc,
                     kOtcryptoAesOperationEncrypt, &input,
                     kOtcryptoAesPaddingNull, &output)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Test key integrity checksum failure
  otcrypto_blinded_key_t bad_key = key;
  bad_key.checksum ^= 0xFFFFFFFF;
  CHECK(otcrypto_aes(&bad_key, &iv, kOtcryptoAesModeCbc,
                     kOtcryptoAesOperationEncrypt, &input,
                     kOtcryptoAesPaddingNull, &output)
            .value == OTCRYPTO_BAD_ARGS.value);

  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t result = OK_STATUS();

  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));

  for (size_t i = 0; i < ARRAYSIZE(kAesTests); i++) {
    LOG_INFO("Starting AES test %d of %d...", i + 1, ARRAYSIZE(kAesTests));
    test = &kAesTests[i];
    EXECUTE_TEST(result, encrypt_test);
    EXECUTE_TEST(result, decrypt_test);
    EXECUTE_TEST(result, encrypt_streaming_test);
    EXECUTE_TEST(result, decrypt_streaming_test);
    LOG_INFO("Finished AES test %d.", i + 1);
  }

  EXECUTE_TEST(result, run_negative_tests);

  return status_ok(result);
}
