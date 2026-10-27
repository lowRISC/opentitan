// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/cryptolib_build_info.h"
#include "sw/device/lib/crypto/include/entropy_src.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/tdes.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/crypto/tdes_testvectors.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

// Random mask for testing.
static const uint32_t kKeyMask[6] = {
    0x1b81540c, 0x220733c9, 0x8bf85383, 0x05ab50b4, 0x8acdcb7e, 0x15e76440,
};

// Global pointer to the current test.
static const tdes_test_t *current_test = NULL;

enum {
  kTdesBlockBytes = 64 / 8,
  kTdesBlockWords = kTdesBlockBytes / sizeof(uint32_t),
};

static otcrypto_key_config_t make_key_config(
    const tdes_test_t *test, otcrypto_key_security_level_t security_level) {
  otcrypto_key_mode_t key_mode;
  switch (test->mode) {
    case kOtcryptoTdesModeEcb:
      LOG_INFO("Mode: ECB");
      key_mode = kOtcryptoKeyModeTdesEcb;
      break;
    case kOtcryptoTdesModeCbc:
      LOG_INFO("Mode: CBC");
      key_mode = kOtcryptoKeyModeTdesCbc;
      break;
    case kOtcryptoTdesModeCfb:
      LOG_INFO("Mode: CFB");
      key_mode = kOtcryptoKeyModeTdesCfb;
      break;
    case kOtcryptoTdesModeOfb:
      LOG_INFO("Mode: OFB");
      key_mode = kOtcryptoKeyModeTdesOfb;
      break;
    case kOtcryptoTdesModeCtr:
      LOG_INFO("Mode: CTR");
      key_mode = kOtcryptoKeyModeTdesCtr;
      break;
    default:
      // Should be unreachable.
      CHECK(false, "Invalid block cipher mode.");
  };

  return (otcrypto_key_config_t){
      .version = otcrypto_lib_version(),
      .key_mode = key_mode,
      .key_length = test->key_len,
      .hw_backed = kHardenedBoolFalse,
      .security_level = security_level,
  };
}

/**
 * Run TDES encryption for the given test vector.
 *
 * If `streaming` is true, we will process the plaintext in small chunks to
 * ensure that the IV is updating correctly.
 *
 * @param test Test vector to run.
 * @param streaming Whether to run in streaming mode.
 */
static status_t run_encrypt(const tdes_test_t *test, bool streaming) {
  // Determine the key configuration.
  otcrypto_key_config_t config =
      make_key_config(test, kOtcryptoKeySecurityLevelLow);

  // Construct blinded key from the key and testing mask.
  uint32_t keyblob[keyblob_num_words(config)];
  TRY(keyblob_from_key_and_mask(test->key, kKeyMask, config, keyblob));
  otcrypto_blinded_key_t key = {
      .config = config,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  key.checksum = otcrypto_integrity_blinded_checksum(&key);

  // Construct a buffer to hold the IV (or NULL for ECB mode).
  uint32_t iv_data[kTdesBlockWords];
  memcpy(iv_data, test->iv, kTdesBlockBytes);
  otcrypto_word32_buf_t iv =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, iv_data, kTdesBlockWords);
  otcrypto_word32_buf_t *iv_ptr =
      (test->mode == kOtcryptoTdesModeEcb) ? NULL : &iv;

  // Calculate the size of the padded plaintext.
  size_t padded_len_bytes;
  TRY(otcrypto_tdes_padded_plaintext_length(test->plaintext_len, test->padding,
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
    while (plaintext_len > kTdesBlockBytes) {
      otcrypto_const_byte_buf_t plaintext_block = OTCRYPTO_MAKE_BUF(
          otcrypto_const_byte_buf_t, plaintext, kTdesBlockBytes);
      otcrypto_byte_buf_t ciphertext_block =
          OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, ciphertext, kTdesBlockBytes);
      TRY(otcrypto_tdes(&key, iv_ptr, test->mode, kOtcryptoTdesOperationEncrypt,
                        &plaintext_block, kOtcryptoTdesPaddingNull,
                        &ciphertext_block));
      plaintext += kTdesBlockBytes;
      ciphertext += kTdesBlockBytes;
      plaintext_len -= kTdesBlockBytes;
      ciphertext_len -= kTdesBlockBytes;
    }
  }

  // Encrypt the remaining input in one shot with the requested padding.
  otcrypto_const_byte_buf_t plaintext_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, plaintext, plaintext_len);
  otcrypto_byte_buf_t ciphertext_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, ciphertext, ciphertext_len);
  TRY(otcrypto_tdes(&key, iv_ptr, test->mode, kOtcryptoTdesOperationEncrypt,
                    &plaintext_buf, test->padding, &ciphertext_buf));

  TRY_CHECK_ARRAYS_EQ(ciphertext_data, test->exp_ciphertext,
                      ARRAYSIZE(ciphertext_data));
  return OK_STATUS();
}

/**
 * Run TDES decryption for the given test vector.
 *
 * If `streaming` is true, we will process the ciphertext in small chunks to
 * ensure that the IV is updating correctly.
 *
 * @param test Test vector to run.
 * @param streaming Whether to run in streaming mode.
 * @param security_level Security level of the key.
 */
static status_t run_decrypt(const tdes_test_t *test, bool streaming,
                            otcrypto_key_security_level_t security_level) {
  // Determine the key configuration.
  otcrypto_key_config_t config = make_key_config(test, security_level);

  // Construct blinded key from the key and testing mask.
  uint32_t keyblob[keyblob_num_words(config)];
  TRY(keyblob_from_key_and_mask(test->key, kKeyMask, config, keyblob));
  otcrypto_blinded_key_t key = {
      .config = config,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  key.checksum = otcrypto_integrity_blinded_checksum(&key);

  // Construct a buffer to hold the IV (or NULL for ECB mode).
  uint32_t iv_data[kTdesBlockWords];
  memcpy(iv_data, test->iv, kTdesBlockBytes);
  otcrypto_word32_buf_t iv =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, iv_data, kTdesBlockWords);
  otcrypto_word32_buf_t *iv_ptr =
      (test->mode == kOtcryptoTdesModeEcb) ? NULL : &iv;

  // Calculate the size of the padded plaintext.
  size_t padded_len_bytes;
  TRY(otcrypto_tdes_padded_plaintext_length(test->plaintext_len, test->padding,
                                            &padded_len_bytes));

  // Construct a buffer for the recovered plaintext.
  TRY_CHECK(padded_len_bytes % sizeof(uint32_t) == 0);
  size_t padded_len_words = padded_len_bytes / sizeof(uint32_t);
  uint32_t recovered_plaintext_data[padded_len_words];
  memset(recovered_plaintext_data, 0, sizeof(recovered_plaintext_data));
  otcrypto_byte_buf_t recovered_plaintext_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t,
                        (uint8_t *)recovered_plaintext_data, padded_len_bytes);

  // If in streaming mode, decrypt one block at a time with null padding until
  // there is only 1 block of input remaining.
  size_t len = sizeof(recovered_plaintext_data);
  const unsigned char *ciphertext = (const unsigned char *)test->exp_ciphertext;
  unsigned char *recovered_plaintext =
      (unsigned char *)recovered_plaintext_data;
  if (streaming) {
    while (len > kTdesBlockBytes) {
      otcrypto_const_byte_buf_t ciphertext_block = OTCRYPTO_MAKE_BUF(
          otcrypto_const_byte_buf_t, ciphertext, kTdesBlockBytes);
      otcrypto_byte_buf_t recovered_plaintext_block = OTCRYPTO_MAKE_BUF(
          otcrypto_byte_buf_t, recovered_plaintext, kTdesBlockBytes);
      TRY(otcrypto_tdes(&key, iv_ptr, test->mode, kOtcryptoTdesOperationDecrypt,
                        &ciphertext_block, kOtcryptoTdesPaddingNull,
                        &recovered_plaintext_block));
      ciphertext += kTdesBlockBytes;
      recovered_plaintext += kTdesBlockBytes;
      len -= kTdesBlockBytes;
    }
    // Expect that the length is now_exactly one block, since the ciphertext
    // length should be a multiple of the block size.
    TRY_CHECK(len == kTdesBlockBytes);
  }

  // Decrypt the remaining input in one shot.
  otcrypto_const_byte_buf_t ciphertext_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, ciphertext, len);
  otcrypto_byte_buf_t recovered_plaintext_buf_last_block =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, recovered_plaintext, len);
  TRY(otcrypto_tdes(&key, iv_ptr, test->mode, kOtcryptoTdesOperationDecrypt,
                    &ciphertext_buf, test->padding,
                    &recovered_plaintext_buf_last_block));
  // Check the result (not including padding).
  TRY_CHECK_ARRAYS_EQ((unsigned char *)recovered_plaintext_data,
                      (unsigned char *)test->plaintext, test->plaintext_len);

  if (test->padding != kOtcryptoTdesPaddingNull) {
    size_t plaintext_len_from_padding;
    TRY(otcrypto_tdes_padding_strip(&recovered_plaintext_buf, test->padding,
                                    &plaintext_len_from_padding));
    TRY_CHECK(plaintext_len_from_padding == test->plaintext_len);
  }

  return OK_STATUS();
}

/**
 * Test one-shot TDES encryption.
 */
static status_t encrypt_test(void) {
  return run_encrypt(current_test, /*streaming=*/false);
}

/**
 * Test one-shot TDES decryption.
 */
static status_t decrypt_test(void) {
  return run_decrypt(current_test, /*streaming=*/false,
                     kOtcryptoKeySecurityLevelLow);
}

/**
 * Test streaming TDES encryption.
 */
static status_t encrypt_streaming_test(void) {
  return run_encrypt(current_test, /*streaming=*/true);
}

/**
 * Test streaming TDES decryption.
 */
static status_t decrypt_streaming_test(void) {
  return run_decrypt(current_test, /*streaming=*/true,
                     kOtcryptoKeySecurityLevelLow);
}

/**
 * Negative tests.
 */
static status_t run_negative_tests(void) {
  LOG_INFO("Running negative tests for TDES API...");

  otcrypto_key_config_t config = {
      .version = otcrypto_lib_version(),
      .key_mode = kOtcryptoKeyModeTdesCbc,
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
  key.checksum = otcrypto_integrity_blinded_checksum(&key);

  uint32_t iv_data[kTdesBlockWords] = {0};
  otcrypto_word32_buf_t iv =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, iv_data, kTdesBlockWords);

  uint8_t input_data[8] = {0};
  otcrypto_const_byte_buf_t input = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, input_data, sizeof(input_data));

  uint8_t output_data[16] = {0};
  otcrypto_byte_buf_t output =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, output_data, 8);

  // Test NULL pointers
  CHECK(otcrypto_tdes(NULL, &iv, kOtcryptoTdesModeCbc,
                      kOtcryptoTdesOperationEncrypt, &input,
                      kOtcryptoTdesPaddingNull, &output)
            .value == OTCRYPTO_BAD_ARGS.value);
  otcrypto_word32_buf_t bad_iv =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, NULL, kTdesBlockWords);
  CHECK(otcrypto_tdes(&key, &bad_iv, kOtcryptoTdesModeCbc,
                      kOtcryptoTdesOperationEncrypt, &input,
                      kOtcryptoTdesPaddingNull, &output)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Test decryption with invalid length
  otcrypto_const_byte_buf_t bad_len_input =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, input_data, 7);
  CHECK(otcrypto_tdes(&key, &iv, kOtcryptoTdesModeCbc,
                      kOtcryptoTdesOperationDecrypt, &bad_len_input,
                      kOtcryptoTdesPaddingNull, &output)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Test null padding with an unaligned input length
  CHECK(otcrypto_tdes(&key, &iv, kOtcryptoTdesModeCbc,
                      kOtcryptoTdesOperationEncrypt, &bad_len_input,
                      kOtcryptoTdesPaddingNull, &output)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Test output buffer length mismatch
  otcrypto_byte_buf_t bad_len_output =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, output_data, 16);
  CHECK(otcrypto_tdes(&key, &iv, kOtcryptoTdesModeCbc,
                      kOtcryptoTdesOperationEncrypt, &input,
                      kOtcryptoTdesPaddingNull, &bad_len_output)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Test invalid IV length
  otcrypto_word32_buf_t bad_len_iv =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, iv_data, 1);
  CHECK(otcrypto_tdes(&key, &bad_len_iv, kOtcryptoTdesModeCbc,
                      kOtcryptoTdesOperationEncrypt, &input,
                      kOtcryptoTdesPaddingNull, &output)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Test key integrity checksum failure
  otcrypto_blinded_key_t bad_key = key;
  bad_key.checksum ^= 0xFFFFFFFF;
  CHECK(otcrypto_tdes(&bad_key, &iv, kOtcryptoTdesModeCbc,
                      kOtcryptoTdesOperationEncrypt, &input,
                      kOtcryptoTdesPaddingNull, &output)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Test mode mismatch between the key's internal mode and the requested TDES
  // mode.
  CHECK(otcrypto_tdes(&key, &iv, kOtcryptoTdesModeEcb,
                      kOtcryptoTdesOperationEncrypt, &input,
                      kOtcryptoTdesPaddingNull, &output)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Test padded plaintext length NULL pointer, invalid enum, and overflow.
  size_t padded_len = 0;
  CHECK(
      otcrypto_tdes_padded_plaintext_length(8, kOtcryptoTdesPaddingPkcs7, NULL)
          .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_tdes_padded_plaintext_length(
            8, (otcrypto_tdes_padding_t)0xdeadbeef, &padded_len)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_tdes_padded_plaintext_length(UINT32_MAX - kTdesBlockBytes + 1,
                                              kOtcryptoTdesPaddingPkcs7,
                                              &padded_len)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_tdes_padded_plaintext_length(
            UINT32_MAX, kOtcryptoTdesPaddingIso9797M2, &padded_len)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Test 0-byte plaintext: rejected with null padding or decryption, accepted
  // when encrypting with non-null padding.
  otcrypto_const_byte_buf_t empty_input =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 0);
  CHECK(otcrypto_tdes(&key, &iv, kOtcryptoTdesModeCbc,
                      kOtcryptoTdesOperationEncrypt, &empty_input,
                      kOtcryptoTdesPaddingNull, &output)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_tdes(&key, &iv, kOtcryptoTdesModeCbc,
                      kOtcryptoTdesOperationDecrypt, &empty_input,
                      kOtcryptoTdesPaddingPkcs7, &output)
            .value == OTCRYPTO_BAD_ARGS.value);
  TRY(otcrypto_tdes_padded_plaintext_length(0, kOtcryptoTdesPaddingPkcs7,
                                            &padded_len));
  TRY_CHECK(padded_len == kTdesBlockBytes);
  TRY(otcrypto_tdes(&key, &iv, kOtcryptoTdesModeCbc,
                    kOtcryptoTdesOperationEncrypt, &empty_input,
                    kOtcryptoTdesPaddingPkcs7, &output));

  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t result = OK_STATUS();
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));

  for (size_t i = 0; i < ARRAYSIZE(kTdesTests); i++) {
    LOG_INFO("Starting TDES test %d of %d...", i + 1, ARRAYSIZE(kTdesTests));
    current_test = &kTdesTests[i];
    EXECUTE_TEST(result, encrypt_test);
    EXECUTE_TEST(result, decrypt_test);
    EXECUTE_TEST(result, encrypt_streaming_test);
    EXECUTE_TEST(result, decrypt_streaming_test);
    LOG_INFO("Finished TDES test %d.", i + 1);
  }

  EXECUTE_TEST(result, run_negative_tests);

  return status_ok(result);
}
