// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/sigverify/mod_exp_ibex.h"

// The autogen rule that creates this header creates it in a directory named
// after the rule, then manipulates the include path in the
// cc_compilation_context to include that directory, so the compiler will find
// the version of this file matching the Bazel rule under test.
#include "sigverify_testvectors.h"

// Index of the test vector currently under test
static uint32_t test_index;

rom_error_t sigverify_mod_exp_ibex_test(void) {
  sigverify_test_vector_t testvec = sigverify_tests[test_index];

  sigverify_rsa_buffer_t recovered_message;
  rom_error_t err =
      sigverify_mod_exp_ibex(&testvec.key, &testvec.sig, &recovered_message);
  if (err != kErrorOk) {
    if (testvec.valid) {
      LOG_ERROR("Error on a valid signature.");
      LOG_INFO("Test notes: %s", testvec.comment);
      return err;
    } else {
      // If a test vector is marked invalid, it's okay to return an error
      return kErrorOk;
    }
  }

  bool passed = memcmp(testvec.encoded_msg, recovered_message.data,
                       sizeof(testvec.encoded_msg)) == 0;
  if (testvec.valid && !passed) {
    // Signature verification failed when it was expected to pass.
    LOG_ERROR("Failed to verify a valid signature.");
    LOG_INFO("Test notes: %s", testvec.comment);
    return kErrorUnknown;
  } else if (!testvec.valid && passed) {
    // Signature verification passed when it was expected to fail.
    LOG_ERROR("Invalid signature passed verification.");
    LOG_INFO("Test notes: %s", testvec.comment);
    return kErrorUnknown;
  }

  return kErrorOk;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t result = OK_STATUS();

  // The definition of `RULE_NAME` comes from the autogen Bazel rule.
  LOG_INFO("Starting mod_exp_ibex_functest:%s", RULE_NAME);
  for (uint32_t i = 0; i < SIGVERIFY_NUM_TESTS; i++) {
    LOG_INFO("Starting test vector %d of %d...", i + 1, SIGVERIFY_NUM_TESTS);
    test_index = i;
    EXECUTE_TEST(result, sigverify_mod_exp_ibex_test);
  }
  LOG_INFO("Finished mod_exp_ibex_functest:%s", RULE_NAME);
  return status_ok(result);
}
