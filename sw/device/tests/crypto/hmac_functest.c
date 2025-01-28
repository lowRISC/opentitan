// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/hmac.h"
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
