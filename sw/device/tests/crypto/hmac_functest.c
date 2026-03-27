// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/hmac.h"
#include "sw/device/lib/crypto/include/keyblob.h"
#include "sw/device/lib/crypto/include/sha2.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// The autogen rule that creates this header creates it in a directory named
// after the rule, then manipulates the include path in the
// cc_compilation_context to include that directory, so the compiler will find
// the version of this file matching the Bazel rule under test.
#include "hmac_testvectors.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

// Global pointer to the current test vector.
static hmac_test_vector_t *current_test_vector = NULL;

/**
 * Run the test pointed to by `current_test_vector`.
 */
static status_t run_test_vector(void) {
  // Populate `checksum` and `config.security_level` fields.
  current_test_vector->key.checksum =
      integrity_blinded_checksum(&current_test_vector->key);

  // The test vectors already have the correct digest sizes hardcoded.
  size_t digest_len = current_test_vector->digest.len;
  // Allocate the buffer for the maximum digest size (which comes from SHA-512).
  uint32_t act_tag[512 / 32];
  otcrypto_word32_buf_t tag_buf = {
      .data = act_tag,
      .len = digest_len,
  };
  otcrypto_hash_digest_t hash_digest = {
      .data = act_tag,
      .len = digest_len,
  };
  switch (current_test_vector->test_operation) {
    case kHmacTestOperationSha256:
      TRY(otcrypto_sha2_256(current_test_vector->message, &hash_digest));
      break;
    case kHmacTestOperationSha384:
      TRY(otcrypto_sha2_384(current_test_vector->message, &hash_digest));
      break;
    case kHmacTestOperationSha512:
      TRY(otcrypto_sha2_512(current_test_vector->message, &hash_digest));
      break;
    case kHmacTestOperationHmacSha256:
      OT_FALLTHROUGH_INTENDED;
    case kHmacTestOperationHmacSha384:
      OT_FALLTHROUGH_INTENDED;
    case kHmacTestOperationHmacSha512:
      TRY(otcrypto_hmac(&current_test_vector->key, current_test_vector->message,
                        tag_buf));
      break;
    default:
      return INVALID_ARGUMENT();
  }
  TRY_CHECK_ARRAYS_EQ(act_tag, current_test_vector->digest.data, digest_len);
  return OK_STATUS();
}

/**
 * Negative tests
 */
static status_t run_negative_tests(void) {
  LOG_INFO("Running HMAC negative tests");

  // Base valid config
  otcrypto_key_config_t valid_cfg = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeHmacSha256,
      .key_length = 32,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };

  // Base valid keyblob
  uint32_t keyblob[keyblob_num_words(valid_cfg)];
  memset(keyblob, 0, sizeof(keyblob));

  otcrypto_blinded_key_t valid_key = {
      .config = valid_cfg,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  valid_key.checksum = integrity_blinded_checksum(&valid_key);

  // Base valid buffers
  uint8_t msg_data[] = "test";
  otcrypto_const_byte_buf_t msg = {.data = msg_data, .len = 4};
  otcrypto_const_byte_buf_t bad_msg = {.data = NULL, .len = 4};

  uint32_t tag_data[8] = {0};
  otcrypto_word32_buf_t tag = {.data = tag_data, .len = 8};
  otcrypto_word32_buf_t bad_tag = {.data = NULL, .len = 8};

  // otcrypto_hmac
  CHECK(otcrypto_hmac(&valid_key, msg, bad_tag).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_hmac(&valid_key, bad_msg, tag).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_hmac(NULL, msg, tag).value == OTCRYPTO_BAD_ARGS.value);

  otcrypto_blinded_key_t bad_key_null = {
      .config = valid_cfg,
      .keyblob_length = sizeof(keyblob),
      .keyblob = NULL,
  };
  CHECK(otcrypto_hmac(&bad_key_null, msg, tag).value ==
        OTCRYPTO_BAD_ARGS.value);

  otcrypto_blinded_key_t bad_key_chk = {
      .config = valid_cfg,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  bad_key_chk.checksum = valid_key.checksum ^ 0xFFFFFFFF;
  CHECK(otcrypto_hmac(&bad_key_chk, msg, tag).value == OTCRYPTO_BAD_ARGS.value);

  otcrypto_key_config_t bad_mode_cfg = valid_cfg;
  bad_mode_cfg.key_mode = kOtcryptoKeyModeAesCtr;
  otcrypto_blinded_key_t bad_key_mode = {
      .config = bad_mode_cfg,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  bad_key_mode.checksum = integrity_blinded_checksum(&bad_key_mode);
  CHECK(otcrypto_hmac(&bad_key_mode, msg, tag).value ==
        OTCRYPTO_BAD_ARGS.value);

  // otcrypto_hmac_init
  otcrypto_hmac_context_t ctx;
  CHECK(otcrypto_hmac_init(NULL, &valid_key).value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_hmac_init(&ctx, NULL).value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_hmac_init(&ctx, &bad_key_null).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_hmac_init(&ctx, &bad_key_chk).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_hmac_init(&ctx, &bad_key_mode).value ==
        OTCRYPTO_BAD_ARGS.value);

  // Setup a valid context
  CHECK(otcrypto_hmac_init(&ctx, &valid_key).value == OTCRYPTO_OK.value);

  // otcrypto_hmac_update
  CHECK(otcrypto_hmac_update(NULL, msg).value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_hmac_update(&ctx, bad_msg).value == OTCRYPTO_BAD_ARGS.value);

  // otcrypto_hmac_final
  CHECK(otcrypto_hmac_final(NULL, tag).value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_hmac_final(&ctx, bad_tag).value == OTCRYPTO_BAD_ARGS.value);

  otcrypto_word32_buf_t bad_tag_len = {.data = tag_data, .len = 7};
  CHECK(otcrypto_hmac_final(&ctx, bad_tag_len).value ==
        OTCRYPTO_BAD_ARGS.value);

  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();
bool test_main(void) {
  LOG_INFO("Testing cryptolib HMAC/SHA-2 streaming implementations.");
  status_t test_result = OK_STATUS();
  // Even though the HMAC IP itself does not need entropy, we need to initialize
  // the entropy complex to be able to clear HMAC with randomness.
  CHECK_STATUS_OK(entropy_complex_init());
  for (size_t i = 0; i < ARRAYSIZE(kHmacTestVectors); i++) {
    current_test_vector = &kHmacTestVectors[i];
    LOG_INFO("Running test %d of %d, test vector identifier: %s", i + 1,
             ARRAYSIZE(kHmacTestVectors),
             current_test_vector->vector_identifier);
    EXECUTE_TEST(test_result, run_test_vector);
  }
  EXECUTE_TEST(test_result, run_negative_tests);
  return status_ok(test_result);
}
