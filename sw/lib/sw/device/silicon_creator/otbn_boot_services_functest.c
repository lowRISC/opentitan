// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/ip/kmac/dif/dif_kmac.h"
#include "sw/lib/sw/device/silicon_creator/otbn_boot_services.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"  // Generated.

OTTF_DEFINE_TEST_CONFIG();

// Message value for signature generation/verification tests.
const char kTestMessage[] = "Test message.";
const size_t kTestMessageLen = sizeof(kTestMessage) - 1;

// Valid ECDSA-P256 public key.
static const attestation_public_key_t kEcdsaKey = {
    .x = {0x1ceb402b, 0x9dc600d1, 0x182ec21b, 0x5ede3640, 0x3566bdac,
          0x1debf94b, 0x1a286a75, 0x8904d749},
    .y = {0x63eab6dc, 0x0c53bf99, 0x086d3ee7, 0x1076efa6, 0x8dd8ece2,
          0xbfececf0, 0x9b94e34d, 0x59b12f3c},
};

// Valid ECDSA-P256 signature for `kTestMessage`.
static const attestation_signature_t kEcdsaSignature = {
    .r = {0x4811545a, 0x088d927b, 0x5d8624b5, 0x2ef1f329, 0x184ba14a,
          0xf655eede, 0xaaed0d54, 0xa20e1ac7},
    .s = {0x729b945d, 0x181dc116, 0x1025dba4, 0xb99828a0, 0xe7225df3,
          0x0e200e9b, 0x785690b4, 0xf47efe98}};

rom_error_t sigverify_test(void) {
  // Hash the test message.
  hmac_digest_t digest;
  hmac_sha256(kTestMessage, kTestMessageLen, &digest);

  // The recovered `r` value from sigverify should be equal to the signature
  // `r` value.
  uint32_t recovered_r[kAttestationSignatureComponentWords];
  RETURN_IF_ERROR(
      otbn_boot_sigverify(&kEcdsaKey, &kEcdsaSignature, &digest, recovered_r));
  CHECK_ARRAYS_EQ(recovered_r, kEcdsaSignature.r, ARRAYSIZE(kEcdsaSignature.r));
  return kErrorOk;
}

bool test_main(void) {
  status_t result = OK_STATUS();

  // Initialize the entropy complex, KMAC, and the key manager.
  CHECK_STATUS_OK(entropy_complex_init());

  // Load the boot services OTBN app.
  CHECK(otbn_boot_app_load() == kErrorOk);

  EXECUTE_TEST(result, sigverify_test);

  return status_ok(result);
}
