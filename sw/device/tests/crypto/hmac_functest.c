// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/hash.h"
#include "sw/device/lib/crypto/include/hmac.h"
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
 * Determines `hash_mode` for given SHA-2 test vectors.
 *
 * Note that for HMAC operations, mode information is part of the key struct,
 * hence this function is only used for hash vectors.
 *
 * @param test_vec The pointer to the test vector.
 * @param[out] hash_mode The determined hash_mode of the given test vector.
 */
static status_t get_hash_mode(hmac_test_vector_t *test_vec,
                              otcrypto_hash_mode_t *hash_mode) {
  switch (test_vec->test_operation) {
    case kHmacTestOperationSha256:
      *hash_mode = kOtcryptoHashModeSha256;
      return OTCRYPTO_OK;
    case kHmacTestOperationSha384:
      *hash_mode = kOtcryptoHashModeSha384;
      return OTCRYPTO_OK;
    case kHmacTestOperationSha512:
      *hash_mode = kOtcryptoHashModeSha512;
      return OTCRYPTO_OK;
    default:
      return OTCRYPTO_BAD_ARGS;
  }
}

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
  uint32_t act_tag[kSha512DigestWords];
  otcrypto_word32_buf_t tag_buf = {
      .data = act_tag,
      .len = digest_len,
  };
  otcrypto_hash_digest_t hash_digest = {
      // .mode is to be determined below in switch-case block.
      .data = act_tag,
      .len = digest_len,
  };
  switch (current_test_vector->test_operation) {
    case kHmacTestOperationSha256:
      OT_FALLTHROUGH_INTENDED;
    case kHmacTestOperationSha384:
      OT_FALLTHROUGH_INTENDED;
    case kHmacTestOperationSha512:
      TRY(get_hash_mode(current_test_vector, &hash_digest.mode));
      TRY(otcrypto_hash(current_test_vector->message, hash_digest));
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
      return OTCRYPTO_BAD_ARGS;
  }
  TRY_CHECK_ARRAYS_EQ(act_tag, current_test_vector->digest.data, digest_len);
  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();
bool test_main(void) {
  LOG_INFO("Testing cryptolib HMAC/SHA-2 streaming implementations.");
  status_t test_result = OK_STATUS();
  for (size_t i = 0; i < ARRAYSIZE(kHmacTestVectors); i++) {
    current_test_vector = &kHmacTestVectors[i];
    LOG_INFO("Running test %d of %d, test vector identifier: %s", i + 1,
             ARRAYSIZE(kHmacTestVectors),
             current_test_vector->vector_identifier);
    EXECUTE_TEST(test_result, run_test_vector);
  }
  return status_ok(test_result);
}
