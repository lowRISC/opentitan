// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/verify.h"

#include <stdint.h>

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/profile.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// The autogen rule that creates this header creates it in a directory named
// after the rule, then manipulates the include path in the
// cc_compilation_context to include that directory, so the compiler will find
// the version of this file matching the Bazel rule under test.
#include "sphincsplus_shake_128s_simple_testvectors.h"

// Index of the test vector currently under test
static uint32_t test_index = 0;

OTTF_DEFINE_TEST_CONFIG();

enum {
  /**
   * Number of negative tests to run (manipulating the message and checking
   * that the signature fails).
   */
  kNumNegativeTests = 1,
};

/**
 * Run the SPHINCS+ verification procedure on the current test.
 *
 * @param test Test vector to run.
 * @param[out] root Output buffer for root node computed from signature.
 * @param[out] pub_root Output buffer for root node computed from public key.
 */
static rom_error_t run_verify(const spx_verify_test_vector_t *test,
                              uint32_t *root, uint32_t *pub_root) {
  // Calculate the public-key root to compare against.
  spx_public_key_root(test->pk, pub_root);

  // Run verification and print the cycle count.
  uint64_t t_start = profile_start();
  rom_error_t err = spx_verify(test->sig, NULL, 0, NULL, 0, test->msg,
                               test->msg_len, test->pk, root);
  uint32_t cycles = profile_end(t_start);
  LOG_INFO("Verification took %u cycles.", cycles);

  return err;
}

/**
 * Run the current test.
 *
 * The verification is expected to succeed.
 */
static rom_error_t spx_verify_test(void) {
  spx_verify_test_vector_t test = spx_verify_tests[test_index];

  uint32_t root[kSpxVerifyRootNumWords];
  uint32_t pub_root[kSpxVerifyRootNumWords];
  RETURN_IF_ERROR(run_verify(&test, root, pub_root));

  // Ensure that both roots are the same (verification passed).
  CHECK_ARRAYS_EQ(root, pub_root, kSpxVerifyRootNumWords);
  return kErrorOk;
}

/**
 * Run the current test with a modified message or signature.
 *
 * The verification is expected to fail.
 */
static rom_error_t spx_verify_negative_test(void) {
  spx_verify_test_vector_t test = spx_verify_tests[test_index];

  if (test.msg_len > 0) {
    // Bitwise-invert the first byte of the message.
    test.msg[0] = ~test.msg[0];
  } else {
    // If the message is empty, change the signature.
    test.sig[0] = ~test.sig[0];
  }

  uint32_t root[kSpxVerifyRootNumWords];
  uint32_t pub_root[kSpxVerifyRootNumWords];
  RETURN_IF_ERROR(run_verify(&test, root, pub_root));

  // Ensure that the roots are the different (verification failed).
  CHECK_ARRAYS_NE(root, pub_root, kSpxVerifyRootNumWords);
  return kErrorOk;
}

bool test_main() {
  status_t result = OK_STATUS();

  CHECK(kNumNegativeTests <= kSpxVerifyNumTests,
        "kNumNegativeTests (%d) cannot be larger than the total number of "
        "tests (%d).",
        kNumNegativeTests, kSpxVerifyNumTests);

  LOG_INFO("Running %d tests with valid signatures.", kSpxVerifyNumTests);

  for (size_t i = 0; i < kSpxVerifyNumTests; i++) {
    EXECUTE_TEST(result, spx_verify_test);
    test_index++;
    LOG_INFO("Finished test %d of %d.", test_index, kSpxVerifyNumTests);
  }

  LOG_INFO("Running %d tests with invalid signatures.", kNumNegativeTests);

  test_index = 0;
  for (size_t i = 0; i < kNumNegativeTests; i++) {
    EXECUTE_TEST(result, spx_verify_negative_test);
    test_index++;
    LOG_INFO("Finished negative test %d of %d.", test_index, kNumNegativeTests);
  }

  return status_ok(result);
}
