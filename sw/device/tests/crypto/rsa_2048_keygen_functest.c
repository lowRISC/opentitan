// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/rsa/rsa_keygen.h"
#include "sw/device/lib/crypto/impl/rsa/rsa_signature.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// Message data for testing.
static const unsigned char kTestMessage[] = "Test message.";
static const size_t kTestMessageLen = sizeof(kTestMessage) - 1;

status_t keygen_then_sign_test(void) {
  // Generate the key pair.
  LOG_INFO("Starting keypair generation...");
  TRY(rsa_keygen_2048_start());
  rsa_2048_public_key_t public_key;
  rsa_2048_private_key_t private_key;
  TRY(rsa_keygen_2048_finalize(&public_key, &private_key));
  LOG_INFO("Keypair generation complete.");
  LOG_INFO("OTBN instruction count: %u", otbn_instruction_count_get());

  // Check that the key uses the F4 exponent.
  TRY_CHECK(public_key.e == 65537);

  // Check that d is at least 2^(len(n) / 2) (this is a FIPS requirement) by
  // ensuring that the most significant half is nonzero.
  bool d_large_enough = false;
  for (size_t i = kRsa2048NumWords / 2; i < kRsa2048NumWords; i++) {
    if (private_key.d.data[i] != 0) {
      d_large_enough = true;
    }
  }
  TRY_CHECK(d_large_enough == true);

  // Generate a signature.
  LOG_INFO("Starting signature generation...");
  TRY(rsa_signature_generate_2048_start(
      &private_key, kTestMessage, kTestMessageLen, kRsaSignaturePaddingPkcs1v15,
      kRsaSignatureHashSha256));
  rsa_2048_int_t signature;
  TRY(rsa_signature_generate_2048_finalize(&signature));
  LOG_INFO("Signature generation complete.");
  LOG_INFO("OTBN instruction count: %u", otbn_instruction_count_get());

  // Try to verify the signature. If something is wrong with the key (nonprime
  // p and q, incorrect d), then this is likely to fail.
  LOG_INFO("Starting signature verification...");
  TRY(rsa_signature_verify_2048_start(&public_key, &signature));
  hardened_bool_t verification_result;
  TRY(rsa_signature_verify_2048_finalize(
      kTestMessage, kTestMessageLen, kRsaSignaturePaddingPkcs1v15,
      kRsaSignatureHashSha256, &verification_result));
  LOG_INFO("Signature verification complete.");
  LOG_INFO("OTBN instruction count: %u", otbn_instruction_count_get());

  // Expect the signature to pass verification.
  TRY_CHECK(verification_result == kHardenedBoolTrue);
  return OK_STATUS();
}

OTTF_DEFINE_TEST_CONFIG();

// Holds the test result.
static volatile status_t test_result;

bool test_main(void) {
  CHECK_STATUS_OK(entropy_testutils_auto_mode_init());

  test_result = OK_STATUS();
  EXECUTE_TEST(test_result, keygen_then_sign_test);
  return status_ok(test_result);
}
