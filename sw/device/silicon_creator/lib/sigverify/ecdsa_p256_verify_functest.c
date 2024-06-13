// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/otbn_boot_services.h"
#include "sw/device/silicon_creator/lib/sigverify/ecdsa_p256_verify.h"

OTTF_DEFINE_TEST_CONFIG();

// Message value for signature generation/verification tests.
const char kTestMessage[] = "Test message.";
const size_t kTestMessageLen = sizeof(kTestMessage) - 1;

// Digest of the test message above.
hmac_digest_t digest;

// Valid ECDSA-P256 public key.
static const ecdsa_p256_public_key_t kEcdsaKey = {
    .x =
        {
            0x1ceb402b,
            0x9dc600d1,
            0x182ec21b,
            0x5ede3640,
            0x3566bdac,
            0x1debf94b,
            0x1a286a75,
            0x8904d749,
        },
    .y =
        {
            0x63eab6dc,
            0x0c53bf99,
            0x086d3ee7,
            0x1076efa6,
            0x8dd8ece2,
            0xbfececf0,
            0x9b94e34d,
            0x59b12f3c,
        },
};

// Valid ECDSA-P256 signature for `kTestMessage`.
static const ecdsa_p256_signature_t kEcdsaSignature = {
    .r =
        {
            0x4811545a,
            0x088d927b,
            0x5d8624b5,
            0x2ef1f329,
            0x184ba14a,
            0xf655eede,
            0xaaed0d54,
            0xa20e1ac7,
        },
    .s =
        {
            0x729b945d,
            0x181dc116,
            0x1025dba4,
            0xb99828a0,
            0xe7225df3,
            0x0e200e9b,
            0x785690b4,
            0xf47efe98,
        },
};

static const ecdsa_p256_signature_t kEcdsaSignatureBad = {
    .r =
        {
            0x481154ff,
            0x088d92ff,
            0x5d8624b5,
            0x2ef1f329,
            0x184ba14a,
            0xf655eede,
            0xaaed0d54,
            0xa20e1ac7,
        },
    .s =
        {
            0x729b945d,
            0x181dc116,
            0x1025dba4,
            0xb99828a0,
            0xe7225df3,
            0x0e200e9b,
            0x785690b4,
            0xf47efe98,
        },
};

rom_error_t ecdsa_p256_verify_ok_test(void) {
  uint32_t flash_exec = 0;
  rom_error_t result = sigverify_ecdsa_p256_verify(&kEcdsaSignature, &kEcdsaKey,
                                                   &digest, &flash_exec);
  CHECK(flash_exec == kSigverifyEcdsaSuccess);
  return result;
}

rom_error_t ecdsa_p256_verify_negative_test(void) {
  uint32_t flash_exec = 0;
  // Signature verification should fail when using the wrong signature.
  if (sigverify_ecdsa_p256_verify(&kEcdsaSignatureBad, &kEcdsaKey, &digest,
                                  &flash_exec) == kErrorOk) {
    return kErrorUnknown;
  }
  CHECK(flash_exec == UINT32_MAX);
  return kErrorOk;
}

bool test_main(void) {
  CHECK(otbn_boot_app_load() == kErrorOk);

  status_t result = OK_STATUS();
  hmac_sha256(kTestMessage, kTestMessageLen, &digest);

  EXECUTE_TEST(result, ecdsa_p256_verify_ok_test);
  EXECUTE_TEST(result, ecdsa_p256_verify_negative_test);
  return status_ok(result);
}
