// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stddef.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/aes_gcm.h"
#include "sw/device/lib/dif/dif_keymgr.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/crypto/aes_gcm_testutils.h"
#include "sw/device/tests/crypto/aes_gcm_testvectors.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

// Global pointer to the current test vector.
const aes_gcm_test_t *current_test = NULL;

static status_t encrypt_test(void) {
  uint32_t cycles;
  TRY(aes_gcm_testutils_encrypt(current_test, /*streaming=*/false, &cycles));
  LOG_INFO("Encrypt cycles: %d", cycles);
  return OK_STATUS();
}

static status_t decrypt_test(void) {
  uint32_t cycles;
  hardened_bool_t tag_valid;
  TRY(aes_gcm_testutils_decrypt(current_test, &tag_valid, /*streaming=*/false,
                                &cycles));
  LOG_INFO("Decrypt cycles: %d", cycles);
  TRY_CHECK(tag_valid == kHardenedBoolTrue);
  return OK_STATUS();
}

static status_t encrypt_streaming_test(void) {
  uint32_t cycles;
  TRY(aes_gcm_testutils_encrypt(current_test, /*streaming=*/true, &cycles));
  LOG_INFO("Encrypt streaming cycles: %d", cycles);
  return OK_STATUS();
}

static status_t decrypt_streaming_test(void) {
  uint32_t cycles;
  hardened_bool_t tag_valid;
  TRY(aes_gcm_testutils_decrypt(current_test, &tag_valid, /*streaming=*/true,
                                &cycles));
  LOG_INFO("Decrypt streaming cycles: %d", cycles);
  TRY_CHECK(tag_valid == kHardenedBoolTrue);
  return OK_STATUS();
}

/**
 * Run negative tests.
 */
static status_t run_bad_args_test(void) {
  LOG_INFO("Running AES-GCM BAD_ARGS negative tests.");

  uint32_t keyblob[8] = {0};
  otcrypto_key_config_t config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeAesGcm,
      .key_length = 32,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  otcrypto_blinded_key_t key = {
      .config = config,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  key.checksum = integrity_blinded_checksum(&key);

  uint32_t iv_data[3] = {0};
  otcrypto_const_word32_buf_t iv = {.data = iv_data, .len = 3};

  uint8_t data[16] = {0};
  otcrypto_const_byte_buf_t pt = {.data = data, .len = 16};
  otcrypto_byte_buf_t ct = {.data = data, .len = 16};

  uint32_t tag_data[4] = {0};
  otcrypto_word32_buf_t tag = {.data = tag_data, .len = 4};

  otcrypto_const_byte_buf_t aad = {.data = NULL, .len = 0};

  // NULL pointer checks
  CHECK(otcrypto_aes_gcm_encrypt(NULL, pt, iv, aad, kOtcryptoAesGcmTagLen128,
                                 ct, tag)
            .value == OTCRYPTO_BAD_ARGS.value);
  otcrypto_word32_buf_t null_tag = {.data = NULL, .len = 4};
  CHECK(otcrypto_aes_gcm_encrypt(&key, pt, iv, aad, kOtcryptoAesGcmTagLen128,
                                 ct, null_tag)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Test length mismatch between plaintext and ciphertext
  otcrypto_byte_buf_t bad_ct = {.data = data, .len = 15};
  CHECK(otcrypto_aes_gcm_encrypt(&key, pt, iv, aad, kOtcryptoAesGcmTagLen128,
                                 bad_ct, tag)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Tag length checks
  otcrypto_word32_buf_t bad_tag_len = {.data = tag_data, .len = 3};
  CHECK(otcrypto_aes_gcm_encrypt(&key, pt, iv, aad, kOtcryptoAesGcmTagLen128,
                                 ct, bad_tag_len)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Invalid tag length enum
  CHECK(otcrypto_aes_gcm_encrypt(&key, pt, iv, aad,
                                 (otcrypto_aes_gcm_tag_len_t)0xFF, ct, tag)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Invalid key mode
  otcrypto_key_config_t bad_mode_config = config;
  bad_mode_config.key_mode = kOtcryptoKeyModeAesCbc;
  otcrypto_blinded_key_t bad_mode_key = {
      .config = bad_mode_config,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  bad_mode_key.checksum = integrity_blinded_checksum(&bad_mode_key);
  CHECK(otcrypto_aes_gcm_encrypt(&bad_mode_key, pt, iv, aad,
                                 kOtcryptoAesGcmTagLen128, ct, tag)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Invalid sideload keyblob length
  otcrypto_key_config_t bad_hw_config = config;
  bad_hw_config.hw_backed = kHardenedBoolTrue;
  otcrypto_blinded_key_t bad_hw_key = {
      .config = bad_hw_config,
      .keyblob_length = 16,  // Wrong size
      .keyblob = keyblob,
  };
  bad_hw_key.checksum = integrity_blinded_checksum(&bad_hw_key);
  CHECK(otcrypto_aes_gcm_encrypt(&bad_hw_key, pt, iv, aad,
                                 kOtcryptoAesGcmTagLen128, ct, tag)
            .value == OTCRYPTO_BAD_ARGS.value);

  return OTCRYPTO_OK;
}

/**
 * Test encryption using sideloading.
 */
static status_t run_sideload_test(void) {
  LOG_INFO("Running AES-GCM Sideload test.");

  dif_keymgr_t keymgr;
  dif_kmac_t kmac;
  TRY(keymgr_testutils_initialize(&keymgr, &kmac));

  uint32_t div_data[16] = {0};

  otcrypto_key_config_t config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeAesGcm,
      .key_length = 32,
      .hw_backed = kHardenedBoolTrue,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };

  otcrypto_blinded_key_t sideload_key = {
      .config = config,
      .keyblob_length = kKeyblobHwBackedBytes,
      .keyblob = div_data,
  };
  sideload_key.checksum = integrity_blinded_checksum(&sideload_key);

  uint32_t iv_data[3] = {0x01020304, 0x05060708, 0x090a0b0c};
  otcrypto_const_word32_buf_t iv = {.data = iv_data, .len = 3};

  uint8_t pt_data[16] = "Sideload test";
  otcrypto_const_byte_buf_t pt = {.data = pt_data, .len = 16};

  uint8_t ct_data[16] = {0};
  otcrypto_byte_buf_t ct = {.data = ct_data, .len = 16};

  uint32_t tag_data[4] = {0};
  otcrypto_word32_buf_t tag = {.data = tag_data, .len = 4};

  otcrypto_const_byte_buf_t aad = {.data = NULL, .len = 0};

  // Encrypt
  TRY(otcrypto_aes_gcm_encrypt(&sideload_key, pt, iv, aad,
                               kOtcryptoAesGcmTagLen128, ct, tag));
  TRY_CHECK(tag_data[0] != 0 || tag_data[1] != 0);

  // Decrypt
  uint8_t recovered_pt_data[16] = {0};
  otcrypto_byte_buf_t recovered_pt = {.data = recovered_pt_data, .len = 16};
  otcrypto_const_byte_buf_t ct_const = {.data = ct.data, .len = ct.len};
  otcrypto_const_word32_buf_t tag_const = {.data = tag.data, .len = tag.len};
  hardened_bool_t success;
  TRY(otcrypto_aes_gcm_decrypt(&sideload_key, ct_const, iv, aad,
                               kOtcryptoAesGcmTagLen128, tag_const,
                               recovered_pt, &success));
  TRY_CHECK(success == kHardenedBoolTrue);
  TRY_CHECK_ARRAYS_EQ(recovered_pt_data, pt_data, 16);

  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t result = OK_STATUS();

  CHECK_STATUS_OK(entropy_complex_init());

  for (size_t i = 0; i < ARRAYSIZE(kAesGcmTestvectors); i++) {
    LOG_INFO("Starting AES-GCM test %d of %d...", i + 1,
             ARRAYSIZE(kAesGcmTestvectors));
    current_test = &kAesGcmTestvectors[i];
    LOG_INFO("Key length = %d", current_test->key_len * sizeof(uint32_t));
    LOG_INFO("Aad length = %d", current_test->aad_len);
    LOG_INFO("Encrypted data length = %d", current_test->plaintext_len);
    LOG_INFO("Tag length = %d", current_test->tag_len);
    EXECUTE_TEST(result, encrypt_test);
    EXECUTE_TEST(result, decrypt_test);
    EXECUTE_TEST(result, encrypt_streaming_test);
    EXECUTE_TEST(result, decrypt_streaming_test);
  }

  EXECUTE_TEST(result, run_sideload_test);
  EXECUTE_TEST(result, run_bad_args_test);

  return status_ok(result);
}
