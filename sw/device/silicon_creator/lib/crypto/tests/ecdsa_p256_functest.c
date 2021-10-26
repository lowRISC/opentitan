// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/crypto/ecdsa_p256/ecdsa_p256.h"
#include "sw/device/silicon_creator/lib/sigverify.h"
#include "sw/device/silicon_creator/lib/test_main.h"

// Message
static const char kMessage[] = "test message";

// Digest of the test message above.
ecdsa_p256_message_digest_t digest;

static const ecdsa_p256_public_key_t kPublicKey = {
    // Public key x-coordinate (Q.x)
    .x = {0x4eb28b55, 0xeb886224, 0xf2bf1b9e, 0xd84a09a7, 0x866792cd,
          0xca075d07, 0x82e72dac, 0x3114791f},
    // Public key y-coordinate (Q.y)
    .y = {0x279ce423, 0x2410a2fa, 0xbd5373f1, 0xa508f040, 0x9ec05521,
          0xa4f05459, 0x003e5f15, 0x3cc64b87},
};

// Private key (d)
static const ecdsa_p256_private_key_t kPrivateKey = {
    .d = {0xcdb457af, 0x1c9f4c74, 0x020c7e8b, 0xe9933e28, 0x0cf0180d,
          0xf46c0bda, 0x7abbe68f, 0xb7a04555},
};

rom_error_t compute_digest(void) {
  hmac_digest_t act_digest;
  uint32_t i;

  hmac_sha256_init();
  RETURN_IF_ERROR(hmac_sha256_update(&kMessage, sizeof(kMessage) - 1));
  RETURN_IF_ERROR(hmac_sha256_final(&act_digest));

  for (i = 0; i < kP256ScalarNumWords; i++) {
    digest.h[i] = act_digest.digest[i];
  };

  return kErrorOk;
}

rom_error_t sign_then_verify_test(void) {
  ecdsa_p256_signature_t signature;
  hardened_bool_t verificationResult;

  // Generate a signature for the message
  LOG_INFO("Signing...");
  RETURN_IF_ERROR(ecdsa_p256_sign(&digest, &kPrivateKey, &signature));

  // Verify the signature
  LOG_INFO("Verifying...");
  RETURN_IF_ERROR(
      ecdsa_p256_verify(&signature, &digest, &kPublicKey, &verificationResult));

  // Signature verification is expected to succeed
  CHECK(verificationResult == kHardenedBoolTrue);

  return kErrorOk;
}

const test_config_t kTestConfig;

bool test_main(void) {
  rom_error_t result = kErrorOk;

  entropy_testutils_boot_mode_init();

  CHECK(compute_digest() == kErrorOk);

  EXECUTE_TEST(result, sign_then_verify_test);
  return result == kErrorOk;
}
