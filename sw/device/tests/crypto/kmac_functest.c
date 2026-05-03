// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/kmac.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/entropy_src.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/kmac.h"
#include "sw/device/lib/crypto/include/sha3.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// The autogen rule that creates this header creates it in a directory named
// after the rule, then manipulates the include path in the
// cc_compilation_context to include that directory, so the compiler will find
// the version of this file matching the Bazel rule under test.
#include "kmac_testvectors.h"

#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

// Global pointer to the current test vector.
static kmac_test_vector_t *current_test_vector = NULL;

/**
 * Get the mode for SHAKE based on the security strength.
 *
 * @param security_str Security strength (in bits).
 * @param[out] mode SHAKE mode enum value.
 */
status_t get_shake_mode(size_t security_strength, otcrypto_hash_mode_t *mode) {
  switch (security_strength) {
    case 128:
      *mode = kOtcryptoHashXofModeShake128;
      break;
    case 256:
      *mode = kOtcryptoHashXofModeShake256;
      break;
    default:
      LOG_INFO("Invalid security strength for SHAKE: %d bits",
               security_strength);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}

/**
 * Get the mode for cSHAKE based on the security strength.
 *
 * @param security_str Security strength (in bits).
 * @param[out] mode cSHAKE mode enum value.
 */
status_t get_cshake_mode(size_t security_strength, otcrypto_hash_mode_t *mode) {
  switch (security_strength) {
    case 128:
      *mode = kOtcryptoHashXofModeCshake128;
      break;
    case 256:
      *mode = kOtcryptoHashXofModeCshake256;
      break;
    default:
      LOG_INFO("Invalid security strength for cSHAKE: %d bits",
               security_strength);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}

/**
 * Get the mode for SHA3 based on the security strength.
 *
 * @param security_str Security strength (in bits).
 * @param[out] mode Hash mode enum value.
 */
status_t get_sha3_mode(size_t security_strength, otcrypto_hash_mode_t *mode) {
  switch (security_strength) {
    case 224:
      *mode = kOtcryptoHashModeSha3_224;
      break;
    case 256:
      *mode = kOtcryptoHashModeSha3_256;
      break;
    case 384:
      *mode = kOtcryptoHashModeSha3_384;
      break;
    case 512:
      *mode = kOtcryptoHashModeSha3_512;
      break;
    default:
      LOG_INFO("Invalid size for SHA3: %d bits", security_strength);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}

/**
 * Call SHA3 to compute the digest.
 *
 * Should only be called when `current_test_vector` is a SHA3 operation.
 *
 * @param[out] digest Computed digest.
 * @return OK or error.
 */
static status_t run_sha3(otcrypto_hash_digest_t *digest) {
  otcrypto_const_byte_buf_t input_msg = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, current_test_vector->input_msg.data,
      current_test_vector->input_msg.len);
  switch (current_test_vector->security_strength) {
    case 224:
      return otcrypto_sha3_224(&input_msg, digest);
    case 256:
      return otcrypto_sha3_256(&input_msg, digest);
    case 384:
      return otcrypto_sha3_384(&input_msg, digest);
    case 512:
      return otcrypto_sha3_512(&input_msg, digest);
    default:
      break;
  }
  LOG_ERROR("Invalid strength for SHA3: %d bits",
            current_test_vector->security_strength);
  return INVALID_ARGUMENT();
}

/**
 * Call SHAKE to compute the digest.
 *
 * Should only be called when `current_test_vector` is a SHAKE operation.
 *
 * @param[out] digest Computed digest.
 * @return OK or error.
 */
static status_t run_shake(otcrypto_hash_digest_t *digest) {
  otcrypto_const_byte_buf_t input_msg = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, current_test_vector->input_msg.data,
      current_test_vector->input_msg.len);
  switch (current_test_vector->security_strength) {
    case 128:
      return otcrypto_shake128(&input_msg, digest);
    case 256:
      return otcrypto_shake256(&input_msg, digest);
    default:
      break;
  }
  LOG_ERROR("Invalid strength for SHAKE: %d bits",
            current_test_vector->security_strength);
  return INVALID_ARGUMENT();
}

/**
 * Call cSHAKE to compute the digest.
 *
 * Should only be called when `current_test_vector` is a cSHAKE operation.
 *
 * @param[out] digest Computed digest.
 * @return OK or error.
 */
static status_t run_cshake(otcrypto_hash_digest_t *digest) {
  otcrypto_const_byte_buf_t input_msg = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, current_test_vector->input_msg.data,
      current_test_vector->input_msg.len);
  otcrypto_const_byte_buf_t func_name = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, current_test_vector->func_name.data,
      current_test_vector->func_name.len);
  otcrypto_const_byte_buf_t cust_str = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, current_test_vector->cust_str.data,
      current_test_vector->cust_str.len);
  switch (current_test_vector->security_strength) {
    case 128:
      return otcrypto_cshake128(&input_msg, &func_name, &cust_str, digest);
    case 256:
      return otcrypto_cshake256(&input_msg, &func_name, &cust_str, digest);
    default:
      break;
  }
  LOG_ERROR("Invalid strength for cSHAKE: %d bits",
            current_test_vector->security_strength);
  return INVALID_ARGUMENT();
}

/**
 * Call KMAC to compute the authentication tag.
 *
 * Should only be called when `current_test_vector` is a KMAC operation.
 *
 * @param[out] tag Computed tag (digest).
 * @return OK or error.
 */
static status_t run_kmac(otcrypto_word32_buf_t tag) {
  current_test_vector->key.checksum =
      integrity_blinded_checksum(&current_test_vector->key);
  otcrypto_const_byte_buf_t input_msg = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, current_test_vector->input_msg.data,
      current_test_vector->input_msg.len);
  otcrypto_const_byte_buf_t cust_str = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, current_test_vector->cust_str.data,
      current_test_vector->cust_str.len);
  return otcrypto_kmac(&current_test_vector->key, &input_msg, &cust_str,
                       current_test_vector->digest.len, &tag);
}

/**
 * Run the test pointed to by `current_test_vector`.
 */
static status_t run_test_vector(void) {
  size_t digest_num_words = current_test_vector->digest.len / sizeof(uint32_t);
  if (current_test_vector->digest.len % sizeof(uint32_t) != 0) {
    digest_num_words++;
  }
  uint32_t digest_data[digest_num_words];
  otcrypto_hash_digest_t digest = {
      .data = digest_data,
      .len = digest_num_words,
  };

  switch (current_test_vector->test_operation) {
    case kKmacTestOperationShake: {
      run_shake(&digest);
      break;
    }
    case kKmacTestOperationCshake: {
      run_cshake(&digest);
      break;
    }
    case kKmacTestOperationSha3: {
      run_sha3(&digest);
      break;
    }
    case kKmacTestOperationKmac: {
      otcrypto_word32_buf_t tag_buf =
          OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, digest.data, digest.len);
      run_kmac(tag_buf);
      break;
    }
    default: {
      LOG_INFO("Unrecognized `operation` field: 0x%04x",
               current_test_vector->test_operation);
      return INVALID_ARGUMENT();
    }
  }

  TRY_CHECK_ARRAYS_EQ((unsigned char *)digest.data,
                      current_test_vector->digest.data,
                      current_test_vector->digest.len);
  return OTCRYPTO_OK;
}

/**
 * Negative tests
 */
static status_t run_negative_tests(void) {
  LOG_INFO("Running KMAC negative tests");

  // Base valid config
  otcrypto_key_config_t valid_cfg = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeKmac128,
      .key_length = 32,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };

  // Base valid keyblob
  uint32_t valid_keyblob[64 / 4] = {0};
  otcrypto_blinded_key_t valid_key = {
      .config = valid_cfg,
      .keyblob_length = sizeof(valid_keyblob),
      .keyblob = valid_keyblob,
  };
  valid_key.checksum = integrity_blinded_checksum(&valid_key);

  // Base valid buffers
  uint8_t dummy_data[] = "test";
  otcrypto_const_byte_buf_t valid_msg =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, dummy_data, 4);
  otcrypto_const_byte_buf_t bad_msg_null =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 4);
  otcrypto_const_byte_buf_t valid_cust =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, dummy_data, 4);
  otcrypto_const_byte_buf_t bad_cust_null =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 4);

  uint32_t tag_data[8] = {0};
  otcrypto_word32_buf_t valid_tag =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, tag_data, 8);
  otcrypto_word32_buf_t bad_tag_null =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, NULL, 8);
  size_t valid_req_len = 32;

  // Null pointer tests
  CHECK(otcrypto_kmac(NULL, &valid_msg, &valid_cust, valid_req_len, &valid_tag)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_kmac(&valid_key, &valid_msg, &valid_cust, valid_req_len,
                      &bad_tag_null)
            .value == OTCRYPTO_BAD_ARGS.value);

  otcrypto_blinded_key_t bad_key_null = {
      .config = valid_cfg,
      .keyblob_length = sizeof(valid_keyblob),
      .keyblob = NULL,
  };
  CHECK(otcrypto_kmac(&bad_key_null, &valid_msg, &valid_cust, valid_req_len,
                      &valid_tag)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Null Data with non-zero length tests
  CHECK(otcrypto_kmac(&valid_key, &bad_msg_null, &valid_cust, valid_req_len,
                      &valid_tag)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_kmac(&valid_key, &valid_msg, &bad_cust_null, valid_req_len,
                      &valid_tag)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Tag and output length checks
  CHECK(
      otcrypto_kmac(&valid_key, &valid_msg, &valid_cust, 0, &valid_tag).value ==
      OTCRYPTO_BAD_ARGS.value);

  // Checksum and mode tests
  otcrypto_blinded_key_t bad_key_chk = {
      .config = valid_cfg,
      .keyblob_length = sizeof(valid_keyblob),
      .keyblob = valid_keyblob,
  };
  bad_key_chk.checksum = valid_key.checksum ^ 0xFFFFFFFF;
  CHECK(otcrypto_kmac(&bad_key_chk, &valid_msg, &valid_cust, valid_req_len,
                      &valid_tag)
            .value == OTCRYPTO_BAD_ARGS.value);

  otcrypto_key_config_t bad_mode_cfg = valid_cfg;
  bad_mode_cfg.key_mode = kOtcryptoKeyModeHmacSha256;
  otcrypto_blinded_key_t bad_key_mode = {
      .config = bad_mode_cfg,
      .keyblob_length = sizeof(valid_keyblob),
      .keyblob = valid_keyblob,
  };
  bad_key_mode.checksum = integrity_blinded_checksum(&bad_key_mode);
  CHECK(otcrypto_kmac(&bad_key_mode, &valid_msg, &valid_cust, valid_req_len,
                      &valid_tag)
            .value == OTCRYPTO_BAD_ARGS.value);

  // SW backed constraints
  otcrypto_blinded_key_t bad_sw_len = {
      .config = valid_cfg,
      .keyblob_length = 32,
      .keyblob = valid_keyblob,
  };
  bad_sw_len.checksum = integrity_blinded_checksum(&bad_sw_len);
  CHECK(otcrypto_kmac(&bad_sw_len, &valid_msg, &valid_cust, valid_req_len,
                      &valid_tag)
            .value == OTCRYPTO_BAD_ARGS.value);

  // HW backed constraints
  otcrypto_key_config_t bad_hw_enum_cfg = valid_cfg;
  bad_hw_enum_cfg.hw_backed = 0xFF;
  otcrypto_blinded_key_t bad_hw_enum = {
      .config = bad_hw_enum_cfg,
      .keyblob_length = sizeof(valid_keyblob),
      .keyblob = valid_keyblob,
  };
  bad_hw_enum.checksum = integrity_blinded_checksum(&bad_hw_enum);
  CHECK(otcrypto_kmac(&bad_hw_enum, &valid_msg, &valid_cust, valid_req_len,
                      &valid_tag)
            .value == OTCRYPTO_BAD_ARGS.value);

  otcrypto_key_config_t bad_hw_len_cfg = valid_cfg;
  bad_hw_len_cfg.hw_backed = kHardenedBoolTrue;
  bad_hw_len_cfg.key_length = 16;
  otcrypto_blinded_key_t bad_hw_len = {
      .config = bad_hw_len_cfg,
      .keyblob_length = 32,
      .keyblob = valid_keyblob,
  };
  bad_hw_len.checksum = integrity_blinded_checksum(&bad_hw_len);
  CHECK(otcrypto_kmac(&bad_hw_len, &valid_msg, &valid_cust, valid_req_len,
                      &valid_tag)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Set up valid buffers for all strict SHA3 lengths
  uint32_t digest_buf_224[7] = {0};   // 224 bits = 7 words
  uint32_t digest_buf_256[8] = {0};   // 256 bits = 8 words
  uint32_t digest_buf_384[12] = {0};  // 384 bits = 12 words
  uint32_t digest_buf_512[16] = {0};  // 512 bits = 16 words

  otcrypto_hash_digest_t valid_sha3_224_digest = {.data = digest_buf_224,
                                                  .len = 7};
  otcrypto_hash_digest_t valid_sha3_256_digest = {.data = digest_buf_256,
                                                  .len = 8};
  otcrypto_hash_digest_t valid_sha3_384_digest = {.data = digest_buf_384,
                                                  .len = 12};
  otcrypto_hash_digest_t valid_sha3_512_digest = {.data = digest_buf_512,
                                                  .len = 16};

  // Generic buffer for SHAKE/cSHAKE tests
  otcrypto_hash_digest_t valid_xof_digest = {.data = digest_buf_256, .len = 8};

  // Reusable bad digests
  otcrypto_hash_digest_t bad_digest_null_data = {.data = NULL, .len = 8};

  // Null digest pointer checks
  CHECK(otcrypto_sha3_224(&valid_msg, NULL).value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_sha3_256(&valid_msg, NULL).value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_sha3_384(&valid_msg, NULL).value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_sha3_512(&valid_msg, NULL).value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_shake128(&valid_msg, NULL).value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_shake256(&valid_msg, NULL).value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_cshake128(&valid_msg, &valid_cust, &valid_cust, NULL).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_cshake256(&valid_msg, &valid_cust, &valid_cust, NULL).value ==
        OTCRYPTO_BAD_ARGS.value);

  // Null data inside digest struct checks
  CHECK(otcrypto_sha3_224(&valid_msg, &bad_digest_null_data).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_sha3_256(&valid_msg, &bad_digest_null_data).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_sha3_384(&valid_msg, &bad_digest_null_data).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_sha3_512(&valid_msg, &bad_digest_null_data).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_shake128(&valid_msg, &bad_digest_null_data).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_shake256(&valid_msg, &bad_digest_null_data).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_cshake128(&valid_msg, &valid_cust, &valid_cust,
                           &bad_digest_null_data)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_cshake256(&valid_msg, &valid_cust, &valid_cust,
                           &bad_digest_null_data)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Null message data with non-zero length checks
  CHECK(otcrypto_sha3_224(&bad_msg_null, &valid_sha3_224_digest).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_sha3_256(&bad_msg_null, &valid_sha3_256_digest).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_sha3_384(&bad_msg_null, &valid_sha3_384_digest).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_sha3_512(&bad_msg_null, &valid_sha3_512_digest).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_shake128(&bad_msg_null, &valid_xof_digest).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_shake256(&bad_msg_null, &valid_xof_digest).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_cshake128(&bad_msg_null, &valid_cust, &valid_cust,
                           &valid_xof_digest)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_cshake256(&bad_msg_null, &valid_cust, &valid_cust,
                           &valid_xof_digest)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Bad length for strict SHA3 functions
  otcrypto_hash_digest_t bad_sha3_224_digest_len = {.data = digest_buf_224,
                                                    .len = 6};
  otcrypto_hash_digest_t bad_sha3_256_digest_len = {.data = digest_buf_256,
                                                    .len = 7};
  otcrypto_hash_digest_t bad_sha3_384_digest_len = {.data = digest_buf_384,
                                                    .len = 11};
  otcrypto_hash_digest_t bad_sha3_512_digest_len = {.data = digest_buf_512,
                                                    .len = 15};

  CHECK(otcrypto_sha3_224(&valid_msg, &bad_sha3_224_digest_len).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_sha3_256(&valid_msg, &bad_sha3_256_digest_len).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_sha3_384(&valid_msg, &bad_sha3_384_digest_len).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_sha3_512(&valid_msg, &bad_sha3_512_digest_len).value ==
        OTCRYPTO_BAD_ARGS.value);

  CHECK(otcrypto_cshake128(&valid_msg, &bad_msg_null, &valid_cust,
                           &valid_xof_digest)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_cshake128(&valid_msg, &valid_cust, &bad_msg_null,
                           &valid_xof_digest)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_cshake256(&valid_msg, &bad_msg_null, &valid_cust,
                           &valid_xof_digest)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_cshake256(&valid_msg, &valid_cust, &bad_msg_null,
                           &valid_xof_digest)
            .value == OTCRYPTO_BAD_ARGS.value);

  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();
bool test_main(void) {
  LOG_INFO("Testing cryptolib KMAC driver.");

  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));
  // Initialize the core with default parameters
  CHECK_STATUS_OK(kmac_hwip_default_configure());

  status_t test_result = OK_STATUS();
  for (size_t i = 0; i < ARRAYSIZE(kKmacTestVectors); i++) {
    current_test_vector = &kKmacTestVectors[i];
    LOG_INFO("Running test %d of %d, test vector identifier: %s", i + 1,
             ARRAYSIZE(kKmacTestVectors),
             current_test_vector->vector_identifier);
    EXECUTE_TEST(test_result, run_test_vector);
  }
  EXECUTE_TEST(test_result, run_negative_tests);
  return status_ok(test_result);
}
