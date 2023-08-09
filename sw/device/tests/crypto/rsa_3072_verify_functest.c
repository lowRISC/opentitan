// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/rsa/rsa_3072_verify.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// The autogen rule that creates this header creates it in a directory named
// after the rule, then manipulates the include path in the
// cc_compilation_context to include that directory, so the compiler will find
// the version of this file matching the Bazel rule under test.
#include "rsa_3072_verify_testvectors.h"

status_t rsa_3072_verify_test(const rsa_3072_verify_test_vector_t *testvec) {
  // Encode message
  rsa_3072_int_t encodedMessage;
  CHECK_STATUS_OK(
      rsa_3072_encode_sha256(testvec->msg, testvec->msgLen, &encodedMessage));

  // Precompute Montgomery constants
  rsa_3072_constants_t constants;
  TRY(rsa_3072_compute_constants(&testvec->publicKey, &constants));

  // Attempt to verify signature
  hardened_bool_t result;
  status_t err = rsa_3072_verify(&testvec->signature, &encodedMessage,
                                 &testvec->publicKey, &constants, &result);

  if (testvec->valid) {
    // Return the error value if not OK.
    TRY(err);
    // Check result.
    if (result != kHardenedBoolTrue) {
      LOG_ERROR("Valid signature failed verification.");
      return OTCRYPTO_RECOV_ERR;
    }
  } else {
    // Signature is expected to be invalid.
    if (result != kHardenedBoolFalse) {
      LOG_ERROR("Invalid signature passed verification.");
      return OTCRYPTO_RECOV_ERR;
    }
    // Error code may be OK or BAD_ARGS, but other errors indicate a problem.
    if (!status_ok(err) && err.value != kCryptoStatusBadArgs) {
      LOG_ERROR("Unexpected error on invalid signature: %r.", err);
      return err;
    }
  }

  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  // Stays true only if all tests pass.
  bool result = true;

  // Set entropy complex to auto mode.
  CHECK_STATUS_OK(entropy_complex_init());

  // The definition of `RULE_NAME` comes from the autogen Bazel rule.
  LOG_INFO("Starting rsa_3072_verify_test:%s", RULE_NAME);
  for (uint32_t i = 0; i < RSA_3072_VERIFY_NUM_TESTS; i++) {
    LOG_INFO("Starting rsa_3072_verify_test on test vector %d of %d...", i + 1,
             RSA_3072_VERIFY_NUM_TESTS);

    // Extract test vector and check for unsupported exponents (e.g. 3); these
    // signatures are expected to fail verification, so mark them invalid.
    rsa_3072_verify_test_vector_t testvec = rsa_3072_verify_tests[i];
    if (testvec.publicKey.e != 65537) {
      testvec.valid = false;
    }

    // Run test and print out result.
    status_t err = rsa_3072_verify_test(&testvec);
    if (status_ok(err)) {
      LOG_INFO("Finished rsa_3072_verify_test on test vector %d : ok", i + 1);
    } else {
      LOG_ERROR("Finished rsa_3072_verify_test on test vector %d : error %r",
                i + 1, err);
      // For help with debugging, print the OTBN error bits, instruction
      // count, and test vector notes.
      LOG_INFO("OTBN error bits: 0x%08x", otbn_err_bits_get());
      LOG_INFO("OTBN instruction count: 0x%08x", otbn_instruction_count_get());
      LOG_INFO("Test notes: %s", testvec.comment);
      result = false;
    }
  }
  LOG_INFO("Finished rsa_3072_verify_test:%s", RULE_NAME);

  return result;
}
