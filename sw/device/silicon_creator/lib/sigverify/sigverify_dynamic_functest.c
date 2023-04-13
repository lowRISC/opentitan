// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/sigverify/sigverify.h"

// The autogen rule that creates this header creates it in a directory named
// after the rule, then manipulates the include path in the
// cc_compilation_context to include that directory, so the compiler will find
// the version of this file matching the Bazel rule under test.
#include "sigverify_testvectors.h"

// Index of the test vector currently under test
static uint32_t test_index;

rom_error_t sigverify_test(void) {
  sigverify_test_vector_t testvec = sigverify_tests[test_index];

  // Extract the digest from the encoded message
  hmac_digest_t digest;
  memcpy(digest.digest, testvec.encoded_msg,
         kHmacDigestNumWords * sizeof(uint32_t));

  uint32_t flash_exec = 0;
  rom_error_t result = sigverify_rsa_verify(&testvec.sig, &testvec.key, &digest,
                                            kLcStateRma, &flash_exec);

  rom_error_t test_result;
  if (testvec.valid) {
    CHECK(flash_exec == kSigverifyRsaSuccess);
    if (result == kErrorOk) {
      test_result = kErrorOk;
    } else {
      // Signature verification failed when it was expected to pass.
      LOG_ERROR("Error while attempting to verify a valid signature.");
      LOG_INFO("Test notes: %s", testvec.comment);
      test_result = result;
    }
  } else {
    CHECK(flash_exec == UINT32_MAX);
    if (result == kErrorOk) {
      // Signature verification passed when it was expected to fail.
      LOG_ERROR("Invalid signature passed verification.");
      LOG_INFO("Test notes: %s", testvec.comment);
      test_result = kErrorUnknown;
    } else {
      test_result = kErrorOk;
    }
  }

  return test_result;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t result = OK_STATUS();

  // The definition of `RULE_NAME` comes from the autogen Bazel rule.
  LOG_INFO("Starting sigverify_dynamic_functest:%s", RULE_NAME);
  for (uint32_t i = 0; i < SIGVERIFY_NUM_TESTS; i++) {
    LOG_INFO("Starting test vector %d of %d...", i + 1, SIGVERIFY_NUM_TESTS);
    test_index = i;
    EXECUTE_TEST(result, sigverify_test);
  }
  LOG_INFO("Finished sigverify_dynamic_functest:%s", RULE_NAME);
  return status_ok(result);
}
