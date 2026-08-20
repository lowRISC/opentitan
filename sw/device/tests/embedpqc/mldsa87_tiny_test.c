// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "third_party/embedpqc/mldsa87_tiny.h"

#include <stdbool.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/cert/dice.h"
#include "sw/device/tests/embedpqc/mldsa_test_utils.h"
#include "sw/device/tests/embedpqc/mldsa_testvectors.h"
#include "third_party/embedpqc/ports/mldsa87_tiny_caller.h"

OTTF_DEFINE_TEST_CONFIG();

uint8_t *mldsa_stack_end = &mldsa_stack[MLDSA_STACK_SIZE];

static status_t keygen_test(void) {
  static uint8_t actual_public_key[MLDSA87_PUBLIC_KEY_BYTES] = {0};

  paint_stack();
  mldsa87_tiny_pub_from_seed_with_stack(actual_public_key, kMldsa87PrivateSeed,
                                        mldsa_stack_end);
  const size_t keygen_stack_usage = get_max_stack_usage();
  LOG_INFO("mldsa87_tiny_pub_from_seed stack use: %u bytes",
           (uint32_t)keygen_stack_usage);

  TRY_CHECK_ARRAYS_EQ(actual_public_key, kMldsa87ExpectedPublicKey,
                      MLDSA87_PUBLIC_KEY_BYTES, "Public keys don't match!");
  TRY_CHECK(
      kDiceMldsaAttestationScratchBufferSize >= keygen_stack_usage,
      "ML-DSA 87 tiny keygen uses more buffer space than assigned in firmware");
  LOG_INFO("Keygen test passed!");

  return OK_STATUS();
}

static status_t message_sign_randomizer_test(void) {
  static uint8_t actual_signature[MLDSA87_SIGNATURE_BYTES] = {0};

  paint_stack();
  mldsa87_tiny_sign_with_stack(actual_signature, kMldsa87PrivateSeed,
                               kMldsa87Randomizer, kMldsa87Message,
                               sizeof(kMldsa87Message), mldsa_stack_end);
  const size_t sign_stack_usage = get_max_stack_usage();
  LOG_INFO("mldsa87_tiny_sign stack use: %u bytes", (uint32_t)sign_stack_usage);

  TRY_CHECK_ARRAYS_EQ(actual_signature, kMldsa87RandomizedExpectedSignature,
                      MLDSA87_SIGNATURE_BYTES,
                      "Randomized message signature doesn't match!");
  TRY_CHECK(kDiceMldsaAttestationScratchBufferSize >= sign_stack_usage,
            "ML-DSA 87 tiny randomized message sign uses more buffer space "
            "than assigned in firmware");
  LOG_INFO("Randomized message signature test passed!");
  return OK_STATUS();
}

static status_t message_sign_deterministic_test(void) {
  static uint8_t actual_signature[MLDSA87_SIGNATURE_BYTES] = {0};

  paint_stack();
  mldsa87_tiny_sign_deterministic_with_stack(
      actual_signature, kMldsa87PrivateSeed, kMldsa87Message,
      sizeof(kMldsa87Message), mldsa_stack_end);
  const size_t sign_stack_usage = get_max_stack_usage();
  LOG_INFO("mldsa87_tiny_sign_deterministic stack use: %u bytes",
           (uint32_t)sign_stack_usage);

  TRY_CHECK_ARRAYS_EQ(actual_signature, kMldsa87ExpectedSignature,
                      MLDSA87_SIGNATURE_BYTES,
                      "Deterministic message signature doesn't match!");
  TRY_CHECK(kDiceMldsaAttestationScratchBufferSize >= sign_stack_usage,
            "ML-DSA 87 tiny deterministic message sign uses more buffer space "
            "than assigned in firmware");
  LOG_INFO("Deterministic message signature test passed!");

  return OK_STATUS();
}

static status_t mu_sign_randomizer_test(void) {
  static uint8_t actual_signature[MLDSA87_SIGNATURE_BYTES] = {0};

  paint_stack();
  mldsa87_tiny_sign_mu_with_stack(actual_signature, kMldsa87PrivateSeed,
                                  kMldsa87Randomizer, kMldsa87Mu,
                                  mldsa_stack_end);
  const size_t sign_stack_usage = get_max_stack_usage();
  LOG_INFO("mldsa87_tiny_sign_mu stack use: %u bytes",
           (uint32_t)sign_stack_usage);

  TRY_CHECK_ARRAYS_EQ(actual_signature, kMldsa87RandomizedExpectedSignature,
                      MLDSA87_SIGNATURE_BYTES,
                      "Randomized mu signature doesn't match!");
  TRY_CHECK(kDiceMldsaAttestationScratchBufferSize >= sign_stack_usage,
            "ML-DSA 87 tiny randomized mu sign uses more buffer space than "
            "assigned in firmware");
  LOG_INFO("Randomized mu signature test passed!");

  return OK_STATUS();
}

static status_t mu_sign_deterministic_test(void) {
  static uint8_t actual_signature[MLDSA87_SIGNATURE_BYTES] = {0};

  paint_stack();
  mldsa87_tiny_sign_mu_deterministic_with_stack(
      actual_signature, kMldsa87PrivateSeed, kMldsa87Mu, mldsa_stack_end);
  const size_t sign_stack_usage = get_max_stack_usage();
  LOG_INFO("mldsa87_tiny_sign_mu_deterministic stack use: %u bytes",
           (uint32_t)sign_stack_usage);

  TRY_CHECK_ARRAYS_EQ(actual_signature, kMldsa87ExpectedSignature,
                      MLDSA87_SIGNATURE_BYTES,
                      "Deterministic mu signature doesn't match!");
  TRY_CHECK(kDiceMldsaAttestationScratchBufferSize >= sign_stack_usage,
            "ML-DSA 87 tiny deterministic mu sign uses more buffer space than "
            "assigned in firmware");
  LOG_INFO("Deterministic mu signature test passed!");

  return OK_STATUS();
}

static status_t message_signature_verify_test(void) {
  paint_stack();
  const int verify_status = mldsa87_tiny_verify_with_stack(
      kMldsa87ExpectedPublicKey, kMldsa87ExpectedSignature, kMldsa87Message,
      sizeof(kMldsa87Message), mldsa_stack_end);
  const size_t verify_stack_usage = get_max_stack_usage();
  LOG_INFO("mldsa87_tiny_verify stack use: %u bytes",
           (uint32_t)verify_stack_usage);

  TRY_CHECK(verify_status != 0, "Message signature verification failed!");
  TRY_CHECK(kDiceMldsaAttestationScratchBufferSize >= verify_stack_usage,
            "ML-DSA 87 tiny message verify uses more buffer space than "
            "assigned in firmware");
  LOG_INFO("Message signature verification test passed!");

  return OK_STATUS();
}

static status_t message_randomized_signature_verify_test(void) {
  paint_stack();
  const int verify_status = mldsa87_tiny_verify_with_stack(
      kMldsa87ExpectedPublicKey, kMldsa87RandomizedExpectedSignature,
      kMldsa87Message, sizeof(kMldsa87Message), mldsa_stack_end);
  const size_t verify_stack_usage = get_max_stack_usage();
  LOG_INFO("mldsa87_tiny_verify stack use: %u bytes",
           (uint32_t)verify_stack_usage);

  TRY_CHECK(verify_status != 0,
            "Randomized message signature verification failed!");
  TRY_CHECK(kDiceMldsaAttestationScratchBufferSize >= verify_stack_usage,
            "ML-DSA 87 tiny message verify uses more buffer space than "
            "assigned in firmware");
  LOG_INFO("Randomized message signature verification test passed!");

  return OK_STATUS();
}

static status_t mu_signature_verify_test(void) {
  paint_stack();
  const int verify_status = mldsa87_tiny_verify_mu_with_stack(
      kMldsa87ExpectedPublicKey, kMldsa87ExpectedSignature, kMldsa87Mu,
      mldsa_stack_end);
  const size_t verify_stack_usage = get_max_stack_usage();
  LOG_INFO("mldsa87_tiny_verify_mu stack use: %u bytes",
           (uint32_t)verify_stack_usage);

  TRY_CHECK(verify_status != 0, "mu signature verification failed!");
  TRY_CHECK(kDiceMldsaAttestationScratchBufferSize >= verify_stack_usage,
            "ML-DSA 87 tiny mu verify uses more buffer space than assigned in "
            "firmware");
  LOG_INFO("mu signature verification test passed!");

  return OK_STATUS();
}

static status_t mu_randomized_signature_verify_test(void) {
  paint_stack();
  const int verify_status = mldsa87_tiny_verify_mu_with_stack(
      kMldsa87ExpectedPublicKey, kMldsa87RandomizedExpectedSignature,
      kMldsa87Mu, mldsa_stack_end);
  const size_t verify_stack_usage = get_max_stack_usage();
  LOG_INFO("mldsa87_tiny_verify_mu stack use: %u bytes",
           (uint32_t)verify_stack_usage);

  TRY_CHECK(verify_status != 0, "Randomized mu signature verification failed!");
  TRY_CHECK(kDiceMldsaAttestationScratchBufferSize >= verify_stack_usage,
            "ML-DSA 87 tiny mu verify uses more buffer space than assigned in "
            "firmware");
  LOG_INFO("Randomized mu signature verification test passed!");

  return OK_STATUS();
}

bool test_main(void) {
  LOG_INFO("ML-DSA-87 Tiny tests starting...");

  if (!status_ok(keygen_test())) {
    return false;
  }

  if (!status_ok(message_sign_deterministic_test())) {
    return false;
  }
  if (!status_ok(message_sign_randomizer_test())) {
    return false;
  }

  if (!status_ok(mu_sign_deterministic_test())) {
    return false;
  }
  if (!status_ok(mu_sign_randomizer_test())) {
    return false;
  }

  if (!status_ok(message_signature_verify_test())) {
    return false;
  }
  if (!status_ok(message_randomized_signature_verify_test())) {
    return false;
  }

  if (!status_ok(mu_signature_verify_test())) {
    return false;
  }
  if (!status_ok(mu_randomized_signature_verify_test())) {
    return false;
  }

  LOG_INFO("ML-DSA-87 Tiny tests completed successfully");
  return true;
}
