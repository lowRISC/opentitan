// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/rsa_3072/rsa_3072_verify.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// The autogen rule that creates this header creates it in a directory named
// after the rule, then manipulates the include path in the
// cc_compilation_context to include that directory, so the compiler will find
// the version of this file matching the Bazel rule under test.
#include "rsa_3072_verify_testvectors.h"

bool rsa_3072_verify_test(const rsa_3072_verify_test_vector_t *testvec) {
  // Encode message
  rsa_3072_int_t encodedMessage;
  hmac_error_t encode_err =
      rsa_3072_encode_sha256(testvec->msg, testvec->msgLen, &encodedMessage);
  if (encode_err != kHmacOk) {
    LOG_ERROR("Error from HMAC during message encoding: 0x%08x.", encode_err);
    return false;
  }

  // Precompute Montgomery constants
  rsa_3072_constants_t constants;
  otbn_error_t err =
      rsa_3072_compute_constants(&testvec->publicKey, &constants);
  if (err != kOtbnErrorOk) {
    LOG_ERROR("Error from OTBN while computing constants: 0x%08x.", err);
    return false;
  }

  // Attempt to verify signature
  hardened_bool_t result;
  err = rsa_3072_verify(&testvec->signature, &encodedMessage,
                        &testvec->publicKey, &constants, &result);

  if (testvec->valid) {
    CHECK(err == kOtbnErrorOk);
    CHECK(result == kHardenedBoolTrue);
  } else {
    CHECK(err == kOtbnErrorOk || err == kOtbnErrorInvalidArgument);
    CHECK(result == kHardenedBoolFalse);
  }

  return true;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  // Stays true only if all tests pass.
  bool result = true;

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
    bool local_result = rsa_3072_verify_test(&testvec);
    if (local_result) {
      LOG_INFO("Finished rsa_3072_verify_test on test vector %d : ok", i + 1);
    } else {
      LOG_ERROR("Finished rsa_3072_verify_test on test vector %d : error",
                i + 1);
      LOG_INFO("Test notes: %s", testvec.comment);
    }
    result &= local_result;
  }
  LOG_INFO("Finished rsa_3072_verify_test:%s", RULE_NAME);

  return result;
}
