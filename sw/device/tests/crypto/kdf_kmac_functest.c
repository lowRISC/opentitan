// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/kmac.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/entropy_src.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/key_transport.h"
#include "sw/device/lib/crypto/include/kmac_kdf.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// The autogen rule that creates this header creates it in a directory named
// after the rule, then manipulates the include path in the
// cc_compilation_context to include that directory, so the compiler will find
// the version of this file matching the Bazel rule under test.
#include "kdf_testvectors.h"

// Global pointer to the current test vector.
static kdf_kmac_test_vector_t *current_test_vector = NULL;

/**
 * Run the test pointed to by `current_test_vector`.
 */
static status_t run_test_vector(void) {
  // Below, `km` prefix refers to output_key_material, and
  // `kdk` prefix refers to key derivation key
  size_t km_num_words = current_test_vector->expected_output.len;
  uint32_t km_buffer[2 * km_num_words];

  otcrypto_blinded_key_t output_key_material = {
      .config =
          {
              // The following key_mode is a dummy placeholder. It does not
              // necessarily match the `key_length`.
              .key_mode = kOtcryptoKeyModeKdfKmac128,
              .version = kOtcryptoLibVersion1,
              .key_length = km_num_words * sizeof(uint32_t),
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
              .exportable = kHardenedBoolTrue,
          },
      .keyblob = km_buffer,
      .keyblob_length = sizeof(km_buffer),
  };

  // Populate `checksum` and `config.security_level` fields.
  current_test_vector->key_derivation_key.checksum =
      integrity_blinded_checksum(&current_test_vector->key_derivation_key);

  otcrypto_const_byte_buf_t label_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, current_test_vector->label.data,
      current_test_vector->label.len);
  otcrypto_const_byte_buf_t context_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, current_test_vector->context.data,
      current_test_vector->context.len);

  TRY(otcrypto_kmac_kdf(&current_test_vector->key_derivation_key, &label_buf,
                        &context_buf, &output_key_material));

  HARDENED_CHECK_EQ(integrity_blinded_key_check(&output_key_material),
                    kHardenedBoolTrue);

  // Export the derived blinded key.
  uint32_t km_share0[km_num_words];
  uint32_t km_share1[km_num_words];
  otcrypto_word32_buf_t km_share0_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, km_share0, ARRAYSIZE(km_share0));
  otcrypto_word32_buf_t km_share1_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, km_share1, ARRAYSIZE(km_share1));
  TRY(otcrypto_export_blinded_key(&output_key_material, &km_share0_buf,
                                  &km_share1_buf));

  // Unmask the derived key and compare to the expected value.
  uint32_t actual_output[km_num_words];
  for (size_t i = 0; i < ARRAYSIZE(actual_output); i++) {
    actual_output[i] = km_share0[i] ^ km_share1[i];
  }
  TRY_CHECK_ARRAYS_EQ(actual_output, current_test_vector->expected_output.data,
                      km_num_words);
  return OTCRYPTO_OK;
}

/**
 * Negative tests
 */
static status_t run_kmac_kdf_negative_tests(void) {
  LOG_INFO("Running KMAC KDF negative tests");

  otcrypto_key_config_t kdk_cfg = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeKdfKmac128,
      .key_length = 32,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  otcrypto_key_config_t km_cfg = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeAesCtr,
      .key_length = 32,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };

  uint32_t kdk_blob[keyblob_num_words(kdk_cfg)];
  memset(kdk_blob, 0, sizeof(kdk_blob));
  otcrypto_blinded_key_t valid_kdk = {.config = kdk_cfg,
                                      .keyblob_length = sizeof(kdk_blob),
                                      .keyblob = kdk_blob};
  valid_kdk.checksum = integrity_blinded_checksum(&valid_kdk);

  uint32_t km_blob[keyblob_num_words(km_cfg)];
  memset(km_blob, 0, sizeof(km_blob));
  otcrypto_blinded_key_t valid_km = {
      .config = km_cfg, .keyblob_length = sizeof(km_blob), .keyblob = km_blob};
  valid_km.checksum = integrity_blinded_checksum(&valid_km);

  uint8_t dummy_data[] = "test";
  otcrypto_const_byte_buf_t valid_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, dummy_data, 4);
  otcrypto_const_byte_buf_t bad_buf_null =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 4);

  // Null pointer and length tests
  CHECK(otcrypto_kmac_kdf(&valid_kdk, &valid_buf, &valid_buf, NULL).value ==
        OTCRYPTO_BAD_ARGS.value);

  otcrypto_blinded_key_t bad_km_null = {
      .config = km_cfg, .keyblob_length = sizeof(km_blob), .keyblob = NULL};
  CHECK(otcrypto_kmac_kdf(&valid_kdk, &valid_buf, &valid_buf, &bad_km_null)
            .value == OTCRYPTO_BAD_ARGS.value);

  otcrypto_blinded_key_t bad_kdk_null = {
      .config = kdk_cfg, .keyblob_length = sizeof(kdk_blob), .keyblob = NULL};
  CHECK(otcrypto_kmac_kdf(&bad_kdk_null, &valid_buf, &valid_buf, &valid_km)
            .value == OTCRYPTO_BAD_ARGS.value);

  CHECK(otcrypto_kmac_kdf(&valid_kdk, &bad_buf_null, &valid_buf, &valid_km)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_kmac_kdf(&valid_kdk, &valid_buf, &bad_buf_null, &valid_km)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Checksum and mode tests
  otcrypto_blinded_key_t bad_kdk_chk = {.config = kdk_cfg,
                                        .keyblob_length = sizeof(kdk_blob),
                                        .keyblob = kdk_blob};
  bad_kdk_chk.checksum = valid_kdk.checksum ^ 0xFFFFFFFF;
  CHECK(otcrypto_kmac_kdf(&bad_kdk_chk, &valid_buf, &valid_buf, &valid_km)
            .value == OTCRYPTO_BAD_ARGS.value);

  otcrypto_key_config_t bad_kdk_mode_cfg = kdk_cfg;
  bad_kdk_mode_cfg.key_mode = kOtcryptoKeyModeHmacSha256;
  otcrypto_blinded_key_t bad_kdk_mode = {.config = bad_kdk_mode_cfg,
                                         .keyblob_length = sizeof(kdk_blob),
                                         .keyblob = kdk_blob};
  bad_kdk_mode.checksum = integrity_blinded_checksum(&bad_kdk_mode);
  CHECK(otcrypto_kmac_kdf(&bad_kdk_mode, &valid_buf, &valid_buf, &valid_km)
            .value == OTCRYPTO_BAD_ARGS.value);

  // OKM configuration tests
  otcrypto_key_config_t bad_km_hw_cfg = km_cfg;
  bad_km_hw_cfg.hw_backed = kHardenedBoolTrue;
  otcrypto_blinded_key_t bad_km_hw = {.config = bad_km_hw_cfg,
                                      .keyblob_length = sizeof(km_blob),
                                      .keyblob = km_blob};
  bad_km_hw.checksum = integrity_blinded_checksum(&bad_km_hw);
  CHECK(
      otcrypto_kmac_kdf(&valid_kdk, &valid_buf, &valid_buf, &bad_km_hw).value ==
      OTCRYPTO_BAD_ARGS.value);

  otcrypto_blinded_key_t bad_km_bloblen = {
      .config = km_cfg, .keyblob_length = 99, .keyblob = km_blob};
  bad_km_bloblen.checksum = integrity_blinded_checksum(&bad_km_bloblen);
  CHECK(otcrypto_kmac_kdf(&valid_kdk, &valid_buf, &valid_buf, &bad_km_bloblen)
            .value == OTCRYPTO_BAD_ARGS.value);

  return OTCRYPTO_OK;
}

/**
 * Verify functionality of generating non-word-aligned output keys.
 */
static status_t run_kmac_kdf_non_word_aligned_test(void) {
  LOG_INFO("Running KMAC KDF non-word-aligned length test");

  kdf_kmac_test_vector_t *vec = &kKdfTestVectors[0];

  // Request an odd byte length (e.g. 1 byte less than standard word alignment)
  size_t exact_byte_len = (vec->expected_output.len * sizeof(uint32_t)) - 1;

  otcrypto_key_config_t okm_config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeKdfKmac128,
      .key_length = exact_byte_len,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolTrue,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };

  size_t keyblob_words = keyblob_num_words(okm_config);
  uint32_t km_buffer[keyblob_words];

  otcrypto_blinded_key_t output_key = {
      .config = okm_config,
      .keyblob = km_buffer,
      .keyblob_length = sizeof(km_buffer),
  };

  vec->key_derivation_key.checksum =
      integrity_blinded_checksum(&vec->key_derivation_key);

  otcrypto_const_byte_buf_t label_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, vec->label.data, vec->label.len);
  otcrypto_const_byte_buf_t context_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, vec->context.data, vec->context.len);

  TRY(otcrypto_kmac_kdf(&vec->key_derivation_key, &label_buf, &context_buf,
                        &output_key));

  HARDENED_CHECK_EQ(integrity_blinded_key_check(&output_key),
                    kHardenedBoolTrue);

  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();
bool test_main(void) {
  LOG_INFO("Testing cryptolib KMAC-KDF driver.");

  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));
  // Initialize the core with default parameters
  CHECK_STATUS_OK(kmac_hwip_default_configure());

  status_t test_result = OK_STATUS();
  for (size_t i = 0; i < ARRAYSIZE(kKdfTestVectors); i++) {
    current_test_vector = &kKdfTestVectors[i];
    LOG_INFO("Running test %d of %d, test vector identifier: %s", i + 1,
             ARRAYSIZE(kKdfTestVectors),
             current_test_vector->vector_identifier);
    EXECUTE_TEST(test_result, run_test_vector);
  }

  EXECUTE_TEST(test_result, run_kmac_kdf_non_word_aligned_test);

  EXECUTE_TEST(test_result, run_kmac_kdf_negative_tests);

  return status_ok(test_result);
}
