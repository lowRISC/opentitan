// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/ecdsa_p256/ecdsa_p256.h"

#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/otbn.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// SHA-256 digest of "test message" (digest in little-endian form)
ecdsa_p256_message_digest_t digest = {.h = {0x05468728, 0x3ed0c5ca, 0x025d4fda,
                                            0xcfa3e704, 0x507ce0d8, 0xecb616f6,
                                            0xa0a4a460, 0x3f0a377b}};

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

const test_config_t kTestConfig;

void sign_then_verify_test(void) {
  ecdsa_p256_signature_t signature;
  hardened_bool_t verificationResult;

  // Initialize OTBN context.
  otbn_t otbn;
  CHECK(otbn_init(&otbn, mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR)) ==
        kOtbnOk);
  // Generate a signature for the message
  LOG_INFO("Signing...");
  CHECK(ecdsa_p256_sign(&otbn, &digest, &kPrivateKey, &signature) == kOtbnOk);

  // Verify the signature
  LOG_INFO("Verifying...");
  CHECK(ecdsa_p256_verify(&otbn, &signature, &digest, &kPublicKey,
                          &verificationResult) == kOtbnOk);

  // Signature verification is expected to succeed
  CHECK(verificationResult == kHardenedBoolTrue);

  return;
}

bool test_main(void) {
  entropy_testutils_boot_mode_init();

  sign_then_verify_test();

  return true;
}
