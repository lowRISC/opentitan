// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/hmac.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/ecdsa_p256/ecdsa_p256.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/crypto/ecdsa_p256_verify_testvectors.h"

hmac_error_t compute_digest(size_t msg_len, const uint8_t *msg,
                            ecdsa_p256_message_digest_t *digest) {
  // Compute the SHA-256 digest using the HMAC device.
  hmac_sha256_init();
  hmac_error_t err = hmac_sha256_update(msg, msg_len);
  if (err != kHmacOk) {
    return err;
  }
  hmac_digest_t hmac_digest;
  err = hmac_sha256_final(&hmac_digest);
  if (err != kHmacOk) {
    return err;
  }

  // Copy digest into the destination array.
  memcpy(digest->h, hmac_digest.digest, sizeof(hmac_digest.digest));

  return kHmacOk;
}

bool ecdsa_p256_verify_test(const ecdsa_p256_verify_test_vector_t *testvec) {
  // Hash message.
  ecdsa_p256_message_digest_t digest;
  hmac_error_t hash_err =
      compute_digest(testvec->msg_len, testvec->msg, &digest);
  CHECK(hash_err == kHmacOk, "Error from HMAC during hashing: 0x%08x.",
        hash_err);

  // Attempt to verify signature.
  hardened_bool_t result;
  otbn_error_t err = ecdsa_p256_verify(&testvec->signature, &digest,
                                       &testvec->public_key, &result);
  otbn_err_bits_t err_bits;
  otbn_get_err_bits(&err_bits);
  CHECK(
      err == kOtbnErrorOk,
      "Error from OTBN while verifying signature: 0x%08x. Error bits: 0b%032b",
      err, err_bits);

  // Check if result matches expectation.
  if (testvec->valid) {
    CHECK(result == kHardenedBoolTrue, "Valid signature failed verification.");
  } else {
    CHECK(result == kHardenedBoolFalse,
          "Invalid signature passed verification.");
  }

  return true;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  // Stays true only if all tests pass.
  bool result = true;

  for (uint32_t i = 0; i < kEcdsaP256VerifyNumTests; i++) {
    LOG_INFO("Starting ecdsa_p256_verify_test on test vector %d of %d...",
             i + 1, kEcdsaP256VerifyNumTests);
    // Run test and print out result.
    ecdsa_p256_verify_test_vector_t testvec = ecdsa_p256_verify_tests[i];
    bool local_result = ecdsa_p256_verify_test(&testvec);
    if (local_result) {
      LOG_INFO("Finished ecdsa_p256_verify_test on test vector %d : ok", i + 1);
    } else {
      LOG_ERROR("Finished ecdsa_p256_verify_test on test vector %d : error",
                i + 1);
      LOG_INFO("Test notes: %s", testvec.comment);
    }
    result &= local_result;
  }

  return result;
}
