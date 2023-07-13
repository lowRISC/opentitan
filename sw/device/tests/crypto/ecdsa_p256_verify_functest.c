// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/hmac.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/ecc/ecdsa_p256.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// The autogen rule that creates this header creates it in a directory named
// after the rule, then manipulates the include path in the
// cc_compilation_context to include that directory, so the compiler will find
// the version of this file matching the Bazel rule under test.
#include "ecdsa_p256_verify_testvectors.h"

static void compute_digest(size_t msg_len, const uint8_t *msg,
                           hmac_digest_t *digest) {
  // Compute the SHA-256 digest using the HMAC device.
  hmac_sha_init();
  hmac_update(msg, msg_len);
  hmac_final(digest);
}

status_t ecdsa_p256_verify_test(
    const ecdsa_p256_verify_test_vector_t *testvec) {
  // Hash message.
  hmac_digest_t digest;
  compute_digest(testvec->msg_len, testvec->msg, &digest);

  // Attempt to verify signature.
  TRY(ecdsa_p256_verify_start(&testvec->signature, digest.digest,
                              &testvec->public_key));
  hardened_bool_t result;
  TRY(ecdsa_p256_verify_finalize(&testvec->signature, &result));

  if (testvec->valid && result != kHardenedBoolTrue) {
    LOG_ERROR("Valid signature failed verification.");
    return OTCRYPTO_RECOV_ERR;
  } else if (!testvec->valid && result != kHardenedBoolFalse) {
    LOG_ERROR("Invalid signature passed verification.");
    return OTCRYPTO_RECOV_ERR;
  }

  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  // Stays true only if all tests pass.
  bool result = true;

  // The definition of `RULE_NAME` comes from the autogen Bazel rule.
  LOG_INFO("Starting ecdsa_p256_verify_test:%s", RULE_NAME);
  for (uint32_t i = 0; i < kEcdsaP256VerifyNumTests; i++) {
    LOG_INFO("Starting ecdsa_p256_verify_test on test vector %d of %d...",
             i + 1, kEcdsaP256VerifyNumTests);
    // Run test and print out result.
    ecdsa_p256_verify_test_vector_t testvec = ecdsa_p256_verify_tests[i];
    status_t err = ecdsa_p256_verify_test(&testvec);
    if (status_ok(err)) {
      LOG_INFO("Finished ecdsa_p256_verify_test on test vector %d : ok", i + 1);
    } else {
      LOG_ERROR("Finished ecdsa_p256_verify_test on test vector %d : error %r",
                i + 1, err);
      // For help with debugging, print the OTBN error bits, instruction
      // count, and test vector notes.
      LOG_INFO("OTBN error bits: 0x%08x", otbn_err_bits_get());
      LOG_INFO("OTBN instruction count: 0x%08x", otbn_instruction_count_get());
      LOG_INFO("Test notes: %s", testvec.comment);
      result = false;
    }
  }
  LOG_INFO("Finished ecdsa_p256_verify_test:%s", RULE_NAME);

  return result;
}
