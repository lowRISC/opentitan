// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/hmac.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/ecc/ecdsa_p256.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// Message
static const char kMessage[] = "test message";

// Digest of the test message above.
hmac_digest_t hmac_digest;

static void compute_digest(void) {
  // Compute the SHA-256 digest using the HMAC device.
  hmac_sha256_init();
  hmac_update((unsigned char *)&kMessage, sizeof(kMessage) - 1);
  hmac_final(&hmac_digest);
}

status_t sign_then_verify_test(hardened_bool_t *verificationResult) {
  // Spin until OTBN is idle.
  TRY(otbn_busy_wait_for_done());

  // Generate a keypair.
  LOG_INFO("Generating keypair...");
  TRY(ecdsa_p256_keygen_start());
  p256_masked_scalar_t private_key;
  p256_point_t public_key;
  TRY(ecdsa_p256_keygen_finalize(&private_key, &public_key));

  // Generate a signature for the message.
  LOG_INFO("Signing...");
  TRY(ecdsa_p256_sign_start(hmac_digest.digest, &private_key));
  ecdsa_p256_signature_t signature;
  TRY(ecdsa_p256_sign_finalize(&signature));

  // Verify the signature.
  LOG_INFO("Verifying...");
  TRY(ecdsa_p256_verify_start(&signature, hmac_digest.digest, &public_key));
  TRY(ecdsa_p256_verify_finalize(&signature, verificationResult));

  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  CHECK_STATUS_OK(entropy_testutils_auto_mode_init());

  compute_digest();

  hardened_bool_t verificationResult;
  status_t err = sign_then_verify_test(&verificationResult);
  if (!status_ok(err)) {
    // If there was an error, print the OTBN error bits and instruction count.
    LOG_INFO("OTBN error bits: 0x%08x", otbn_err_bits_get());
    LOG_INFO("OTBN instruction count: 0x%08x", otbn_instruction_count_get());
    // Print the error.
    CHECK_STATUS_OK(err);
    return false;
  }

  // Signature verification is expected to succeed.
  if (verificationResult != kHardenedBoolTrue) {
    LOG_ERROR("Signature failed to pass verification!");
    return false;
  }

  return true;
}
