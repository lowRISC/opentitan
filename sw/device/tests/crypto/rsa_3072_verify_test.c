// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/rsa_3072/rsa_3072_verify.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/runtime/otbn.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_framework/test_main.h"
#include "sw/device/tests/crypto/rsa_3072_verify_testvectors.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

void rsa_3072_verify_test(otbn_t *otbn, dif_hmac_t *hmac,
                          const rsa_3072_verify_test_vector_t *testvec) {
  // Encode message
  rsa_3072_int_t encodedMessage;
  CHECK(rsa_3072_encode_sha256(hmac, testvec->msg, testvec->msgLen,
                               &encodedMessage) == kDifOk);

  // Precompute Montgomery constants
  rsa_3072_constants_t constants;
  CHECK(rsa_3072_compute_constants(otbn, &testvec->publicKey, &constants) ==
        kOtbnOk);

  // Attempt to verify signature
  hardened_bool_t result;
  CHECK(rsa_3072_verify(otbn, &testvec->signature, &encodedMessage,
                        &testvec->publicKey, &constants, &result) == kOtbnOk);

  if (testvec->valid) {
    CHECK(result == kHardenedBoolTrue,
          "Failed to verify an expected-valid signature. Test notes: ",
          testvec->comment);
  } else {
    CHECK(result == kHardenedBoolFalse,
          "Successfully verified an expected-invalid signature. Test notes: ",
          testvec->comment);
  }

  return;
}

const test_config_t kTestConfig;

bool test_main(void) {
  // Initialize OTBN context.
  otbn_t otbn;
  CHECK(otbn_init(&otbn, mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR)) ==
        kOtbnOk);

  // Initialize HMAC context
  dif_hmac_t hmac;
  CHECK(dif_hmac_init(mmio_region_from_addr(TOP_EARLGREY_HMAC_BASE_ADDR),
                      &hmac) == kDifOk);

  for (uint32_t i = 0; i < RSA_3072_VERIFY_NUM_TESTS; i++) {
    LOG_INFO("Starting rsa_3072_verify_test on test vector %d of %d...", i + 1,
             RSA_3072_VERIFY_NUM_TESTS);
    rsa_3072_verify_test(&otbn, &hmac, &rsa_3072_verify_tests[i]);
    LOG_INFO("Finished rsa_3072_verify_test on test vector %d : ok", i + 1);
  }

  return true;
}
