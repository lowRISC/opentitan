// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/hmac.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/ecdsa_p256/ecdsa_p256.h"
#include "sw/device/lib/crypto/impl/otbn_util.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// Message
static const char kMessage[] = "test message";

// Digest of the test message above.
ecdsa_p256_message_digest_t digest;

static const ecdsa_p256_public_key_t kPublicKey = {
    // Public key x-coordinate (Q.x)
    .x = {0x558bb24e, 0x246288eb, 0x9e1bbff2, 0xa7094ad8, 0xcd926786,
          0x075d07ca, 0xac2de782, 0x1f791431},
    // Public key y-coordinate (Q.y)
    .y = {0x23e49c27, 0xfaa21024, 0xf17353bd, 0x40f008a5, 0x2155c09e,
          0x5954f0a4, 0x155f3e00, 0x874bc63c},
};

// Private key (d) in two shares
static const ecdsa_p256_private_key_t kPrivateKey = {
    .d0 = {0xaf57b4cd, 0x744c9f1c, 0x8b7e0c02, 0x283e93e9, 0x0d18f00c,
           0xda0b6cf4, 0x8fe6bb7a, 0x5545a0b7},
    // TODO(#15409): add real data here to ensure the second share is
    // incorporated.
    .d1 = {0},
};

hmac_error_t compute_digest(void) {
  // Compute the SHA-256 digest using the HMAC device.
  hmac_sha256_init();
  hmac_error_t err = hmac_sha256_update(&kMessage, sizeof(kMessage) - 1);
  if (err != kHmacOk) {
    return err;
  }
  hmac_digest_t hmac_digest;
  err = hmac_sha256_final(&hmac_digest);
  if (err != kHmacOk) {
    return err;
  }

  // Copy digest into the destination array.
  memcpy(digest.h, hmac_digest.digest, sizeof(hmac_digest.digest));

  return kHmacOk;
}

bool sign_then_verify_test(void) {
  ecdsa_p256_signature_t signature;
  hardened_bool_t verificationResult;

  // Spin until OTBN is idle.
  if (otbn_busy_wait_for_done() != kOtbnErrorOk) {
    return false;
  }

  // Generate a signature for the message
  LOG_INFO("Signing...");
  otbn_error_t err = ecdsa_p256_sign(&digest, &kPrivateKey, &signature);
  if (err != kOtbnErrorOk) {
    LOG_ERROR("Error from OTBN while signing: 0x%08x.", err);
    otbn_err_bits_t err_bits;
    otbn_err_bits_get(&err_bits);
    LOG_INFO("OTBN error bits: 0x%08x", err_bits);
    return false;
  }

  // Verify the signature
  LOG_INFO("Verifying...");
  err =
      ecdsa_p256_verify(&signature, &digest, &kPublicKey, &verificationResult);
  if (err != kOtbnErrorOk) {
    LOG_ERROR("Error from OTBN while verifying signature: 0x%08x.", err);
    otbn_err_bits_t err_bits;
    otbn_err_bits_get(&err_bits);
    LOG_INFO("OTBN error bits: 0x%08x", err_bits);
    return false;
  }

  // Signature verification is expected to succeed
  CHECK(verificationResult == kHardenedBoolTrue);

  return true;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  entropy_testutils_boot_mode_init();

  CHECK(compute_digest() == kHmacOk);

  return sign_then_verify_test();
}
