// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stddef.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/aes_gcm.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/entropy_src.h"
#include "sw/device/lib/crypto/include/integrity.h"
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

  uint32_t keyblob[16] = {0};
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
  otcrypto_const_word32_buf_t iv =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, iv_data, 3);

  uint8_t data[16] = {0};
  otcrypto_const_byte_buf_t pt =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, data, 16);
  otcrypto_byte_buf_t ct = OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, data, 16);

  uint32_t tag_data[4] = {0};
  otcrypto_word32_buf_t tag =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, tag_data, 4);

  otcrypto_const_byte_buf_t aad =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 0);

  // NULL pointer checks
  CHECK(otcrypto_aes_gcm_encrypt(NULL, &pt, &iv, &aad, kOtcryptoAesGcmTagLen128,
                                 &ct, &tag)
            .value == OTCRYPTO_BAD_ARGS.value);
  otcrypto_word32_buf_t null_tag =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, NULL, 4);
  CHECK(otcrypto_aes_gcm_encrypt(&key, &pt, &iv, &aad, kOtcryptoAesGcmTagLen128,
                                 &ct, &null_tag)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Length mismatch checks
  otcrypto_byte_buf_t bad_ct = OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, data, 15);
  otcrypto_const_byte_buf_t bad_ct_const =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, data, 15);
  otcrypto_const_word32_buf_t tag_const =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, tag_data, 4);
  hardened_bool_t success;

  CHECK(otcrypto_aes_gcm_encrypt(&key, &pt, &iv, &aad, kOtcryptoAesGcmTagLen128,
                                 &bad_ct, &tag)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_aes_gcm_decrypt(&key, &bad_ct_const, &iv, &aad,
                                 kOtcryptoAesGcmTagLen128, &tag_const, &ct,
                                 &success)
            .value == OTCRYPTO_BAD_ARGS.value);

  // IV length checks
  otcrypto_const_word32_buf_t short_iv =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, iv_data, 2);
  CHECK(otcrypto_aes_gcm_encrypt(&key, &pt, &short_iv, &aad,
                                 kOtcryptoAesGcmTagLen128, &ct, &tag)
            .value == OTCRYPTO_BAD_ARGS.value);

  uint32_t long_iv_data[5] = {0};
  otcrypto_const_word32_buf_t long_iv =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, long_iv_data, 5);
  CHECK(otcrypto_aes_gcm_encrypt(&key, &pt, &long_iv, &aad,
                                 kOtcryptoAesGcmTagLen128, &ct, &tag)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Tag length checks
  otcrypto_word32_buf_t bad_tag_len =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, tag_data, 3);
  CHECK(otcrypto_aes_gcm_encrypt(&key, &pt, &iv, &aad, kOtcryptoAesGcmTagLen128,
                                 &ct, &bad_tag_len)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Invalid tag length enum
  CHECK(otcrypto_aes_gcm_encrypt(&key, &pt, &iv, &aad,
                                 (otcrypto_aes_gcm_tag_len_t)0xFF, &ct, &tag)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Key Mode & Integrity Checks
  otcrypto_key_config_t bad_mode_config = config;
  bad_mode_config.key_mode = kOtcryptoKeyModeAesCbc;
  otcrypto_blinded_key_t bad_mode_key = {
      .config = bad_mode_config,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  bad_mode_key.checksum = integrity_blinded_checksum(&bad_mode_key);
  CHECK(otcrypto_aes_gcm_encrypt(&bad_mode_key, &pt, &iv, &aad,
                                 kOtcryptoAesGcmTagLen128, &ct, &tag)
            .value == OTCRYPTO_BAD_ARGS.value);

  otcrypto_key_config_t bad_hw_config = config;
  bad_hw_config.hw_backed = kHardenedBoolTrue;
  otcrypto_blinded_key_t bad_hw_key = {
      .config = bad_hw_config,
      .keyblob_length = 16,  // Wrong size
      .keyblob = keyblob,
  };
  bad_hw_key.checksum = integrity_blinded_checksum(&bad_hw_key);
  CHECK(otcrypto_aes_gcm_encrypt(&bad_hw_key, &pt, &iv, &aad,
                                 kOtcryptoAesGcmTagLen128, &ct, &tag)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Streaming API BAD_ARGS tests
  otcrypto_aes_gcm_context_t ctx;

  // Init checks
  CHECK(otcrypto_aes_gcm_encrypt_init(NULL, &iv, &ctx).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_aes_gcm_encrypt_init(&key, NULL, &ctx).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_aes_gcm_encrypt_init(&key, &iv, NULL).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_aes_gcm_encrypt_init(&key, &short_iv, &ctx).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_aes_gcm_encrypt_init(&key, &long_iv, &ctx).value ==
        OTCRYPTO_BAD_ARGS.value);

  CHECK(otcrypto_aes_gcm_decrypt_init(NULL, &iv, &ctx).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_aes_gcm_decrypt_init(&key, NULL, &ctx).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_aes_gcm_decrypt_init(&key, &iv, NULL).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_aes_gcm_decrypt_init(&key, &short_iv, &ctx).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_aes_gcm_decrypt_init(&key, &long_iv, &ctx).value ==
        OTCRYPTO_BAD_ARGS.value);

  // Initialize a valid context for further testing
  TRY(otcrypto_aes_gcm_encrypt_init(&key, &iv, &ctx));

  // Update AAD checks
  otcrypto_const_byte_buf_t valid_aad =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, data, 16);
  CHECK(otcrypto_aes_gcm_update_aad(NULL, &valid_aad).value ==
        OTCRYPTO_BAD_ARGS.value);
  otcrypto_const_byte_buf_t null_aad_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 5);
  CHECK(otcrypto_aes_gcm_update_aad(&ctx, &null_aad_buf).value ==
        OTCRYPTO_BAD_ARGS.value);

  // Update encrypted data checks
  size_t written;
  CHECK(
      otcrypto_aes_gcm_update_encrypted_data(NULL, &pt, &ct, &written).value ==
      OTCRYPTO_BAD_ARGS.value);
  otcrypto_const_byte_buf_t null_pt =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 16);
  CHECK(otcrypto_aes_gcm_update_encrypted_data(&ctx, &null_pt, &ct, &written)
            .value == OTCRYPTO_BAD_ARGS.value);
  otcrypto_byte_buf_t null_ct =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, NULL, 16);
  CHECK(otcrypto_aes_gcm_update_encrypted_data(&ctx, &pt, &null_ct, &written)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_aes_gcm_update_encrypted_data(&ctx, &pt, &ct, NULL).value ==
        OTCRYPTO_BAD_ARGS.value);

  otcrypto_byte_buf_t short_ct =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, data, 15);
  CHECK(otcrypto_aes_gcm_update_encrypted_data(&ctx, &pt, &short_ct, &written)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Update the key checksum because we remasked before
  key.checksum = integrity_blinded_checksum(&key);

  // Test operation ordering
  otcrypto_aes_gcm_context_t ctx_aad_after_data;
  TRY(otcrypto_aes_gcm_encrypt_init(&key, &iv, &ctx_aad_after_data));
  TRY(otcrypto_aes_gcm_update_encrypted_data(&ctx_aad_after_data, &pt, &ct,
                                             &written));
  // Adding AAD after data has already been accumulated must return BAD_ARGS
  CHECK(otcrypto_aes_gcm_update_aad(&ctx_aad_after_data, &valid_aad).value ==
        OTCRYPTO_BAD_ARGS.value);

  // Encrypt final checks
  CHECK(otcrypto_aes_gcm_encrypt_final(NULL, kOtcryptoAesGcmTagLen128, &ct,
                                       &written, &tag)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_aes_gcm_encrypt_final(&ctx, kOtcryptoAesGcmTagLen128, &ct,
                                       NULL, &tag)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_aes_gcm_encrypt_final(&ctx, kOtcryptoAesGcmTagLen128, &ct,
                                       &written, &null_tag)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Partial block length check in final
  otcrypto_const_byte_buf_t partial_pt =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, data, 10);
  TRY(otcrypto_aes_gcm_update_encrypted_data(
      &ctx, &partial_pt, &ct, &written));  // Push 10 bytes to context
  otcrypto_byte_buf_t too_short_ct_final =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, data, 9);
  CHECK(otcrypto_aes_gcm_encrypt_final(&ctx, kOtcryptoAesGcmTagLen128,
                                       &too_short_ct_final, &written, &tag)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Decrypt final checks
  otcrypto_const_word32_buf_t null_const_tag =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, NULL, 4);
  CHECK(otcrypto_aes_gcm_decrypt_final(
            NULL, &tag_const, kOtcryptoAesGcmTagLen128, &ct, &written, &success)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_aes_gcm_decrypt_final(&ctx, &null_const_tag,
                                       kOtcryptoAesGcmTagLen128, &ct, &written,
                                       &success)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_aes_gcm_decrypt_final(
            &ctx, &tag_const, kOtcryptoAesGcmTagLen128, &ct, NULL, &success)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_aes_gcm_decrypt_final(
            &ctx, &tag_const, kOtcryptoAesGcmTagLen128, &ct, &written, NULL)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Update the key checksum because we remasked before
  key.checksum = integrity_blinded_checksum(&key);

  // Re-init context for decrypt to reset input_len for the partial block test
  TRY(otcrypto_aes_gcm_decrypt_init(&key, &iv, &ctx));
  TRY(otcrypto_aes_gcm_update_encrypted_data(&ctx, &partial_pt, &ct,
                                             &written));  // Push 10 bytes
  CHECK(otcrypto_aes_gcm_decrypt_final(&ctx, &tag_const,
                                       kOtcryptoAesGcmTagLen128,
                                       &too_short_ct_final, &written, &success)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Edge Case & Fault Injection Coverage

  // Failed Decryption Tag Check
  key.checksum = integrity_blinded_checksum(&key);
  TRY(otcrypto_aes_gcm_encrypt(&key, &pt, &iv, &aad, kOtcryptoAesGcmTagLen128,
                               &ct, &tag));
  ct.data[0] ^= 0x01;  // Corrupt ciphertext bit
  otcrypto_const_byte_buf_t ct_const_corrupt =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, ct.data, 16);
  TRY(otcrypto_aes_gcm_decrypt(&key, &ct_const_corrupt, &iv, &aad,
                               kOtcryptoAesGcmTagLen128, &tag_const, &ct,
                               &success));
  CHECK(success == kHardenedBoolFalse);
  ct.data[0] ^= 0x01;

  // Top-Level NULL Pointer Checks
  otcrypto_const_byte_buf_t null_buf_16 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 16);
  otcrypto_byte_buf_t null_out_16 =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, NULL, 16);

  // Just one check per top-level API is enough to light up the coverage lines
  CHECK(otcrypto_aes_gcm_encrypt(&key, &null_buf_16, &iv, &aad,
                                 kOtcryptoAesGcmTagLen128, &ct, &tag)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_aes_gcm_decrypt(&key, &null_buf_16, &iv, &aad,
                                 kOtcryptoAesGcmTagLen128, &tag_const, &ct,
                                 &success)
            .value != OTCRYPTO_OK.value);

  // Inner Driver Bounds & Overflows
  key.checksum = integrity_blinded_checksum(&key);
  TRY(otcrypto_aes_gcm_encrypt_init(&key, &iv, &ctx));

  otcrypto_const_byte_buf_t buf_16 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, data, 16);
  otcrypto_byte_buf_t out_16 = OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, data, 16);
  otcrypto_const_byte_buf_t huge_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, data, UINT32_MAX);

  // Inner AAD Overflow & Inner NULL check
  TRY(otcrypto_aes_gcm_update_aad(&ctx, &buf_16));
  CHECK(otcrypto_aes_gcm_update_aad(&ctx, &huge_buf).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_aes_gcm_update_encrypted_data(&ctx, &null_buf_16, &out_16,
                                               &written)
            .value != OTCRYPTO_OK.value);

  // Inner Data Overflow & Inner Final NULL check
  TRY(otcrypto_aes_gcm_update_encrypted_data(&ctx, &buf_16, &out_16, &written));
  CHECK(
      otcrypto_aes_gcm_update_encrypted_data(&ctx, &huge_buf, &out_16, &written)
          .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_aes_gcm_encrypt_final(&ctx, kOtcryptoAesGcmTagLen128, &out_16,
                                       NULL, &tag)
            .value != OTCRYPTO_OK.value);

  // Final API NULL Checks
  key.checksum = integrity_blinded_checksum(&key);
  TRY(otcrypto_aes_gcm_encrypt_init(&key, &iv, &ctx));
  CHECK(otcrypto_aes_gcm_encrypt_final(&ctx, kOtcryptoAesGcmTagLen128,
                                       &null_out_16, &written, &tag)
            .value != OTCRYPTO_OK.value);

  key.checksum = integrity_blinded_checksum(&key);
  TRY(otcrypto_aes_gcm_decrypt_init(&key, &iv, &ctx));
  CHECK(otcrypto_aes_gcm_decrypt_final(&ctx, &tag_const,
                                       kOtcryptoAesGcmTagLen128, &null_out_16,
                                       &written, &success)
            .value != OTCRYPTO_OK.value);

  // Fault Injection
  key.checksum = integrity_blinded_checksum(&key);
  TRY(otcrypto_aes_gcm_encrypt_init(&key, &iv, &ctx));
  ctx.data[0] = 0xBADBAD;  // Corrupt is_encrypt boolean
  CHECK(otcrypto_aes_gcm_update_encrypted_data(&ctx, &buf_16, &out_16, &written)
            .value != OTCRYPTO_OK.value);

  key.checksum = integrity_blinded_checksum(&key);
  TRY(otcrypto_aes_gcm_encrypt_init(&key, &iv, &ctx));
  ctx.data[1] = 0xBADBAD;  // Corrupt aes_key.mode enum
  CHECK(otcrypto_aes_gcm_update_encrypted_data(&ctx, &buf_16, &out_16, &written)
            .value != OTCRYPTO_OK.value);

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
  otcrypto_const_word32_buf_t iv =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, iv_data, 3);

  uint8_t pt_data[16] = "Sideload test";
  otcrypto_const_byte_buf_t pt =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, pt_data, 16);

  uint8_t ct_data[16] = {0};
  otcrypto_byte_buf_t ct = OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, ct_data, 16);

  uint32_t tag_data[4] = {0};
  otcrypto_word32_buf_t tag =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, tag_data, 4);

  otcrypto_const_byte_buf_t aad =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 0);

  // Encrypt
  TRY(otcrypto_aes_gcm_encrypt(&sideload_key, &pt, &iv, &aad,
                               kOtcryptoAesGcmTagLen128, &ct, &tag));
  TRY_CHECK(tag_data[0] != 0 || tag_data[1] != 0);

  // Decrypt
  uint8_t recovered_pt_data[16] = {0};
  otcrypto_byte_buf_t recovered_pt =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, recovered_pt_data, 16);
  otcrypto_const_byte_buf_t ct_const =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, ct.data, ct.len);
  otcrypto_const_word32_buf_t tag_const =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, tag.data, tag.len);
  hardened_bool_t success;
  TRY(otcrypto_aes_gcm_decrypt(&sideload_key, &ct_const, &iv, &aad,
                               kOtcryptoAesGcmTagLen128, &tag_const,
                               &recovered_pt, &success));
  TRY_CHECK(success == kHardenedBoolTrue);
  TRY_CHECK_ARRAYS_EQ(recovered_pt_data, pt_data, 16);

  otcrypto_aes_gcm_context_t sl_ctx;
  size_t sl_written;
  TRY(otcrypto_aes_gcm_encrypt_init(&sideload_key, &iv, &sl_ctx));
  TRY(otcrypto_aes_gcm_update_aad(&sl_ctx, &pt));
  TRY(otcrypto_aes_gcm_update_encrypted_data(&sl_ctx, &pt, &ct, &sl_written));
  TRY(otcrypto_aes_gcm_encrypt_final(&sl_ctx, kOtcryptoAesGcmTagLen128, &ct,
                                     &sl_written, &tag));

  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t result = OK_STATUS();

  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));

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
