// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/crypto/rsa_3072/rsa_3072_verify.h"
#include "sw/device/lib/crypto/tests/rsa_3072_verify_testvectors.h"
#include "sw/device/lib/drivers/otbn.h"
#include "sw/device/lib/testing/test_framework/ottf.h"

bool rsa_3072_verify_test(const rsa_3072_verify_test_vector_t *testvec) {
  rsa_3072_constants_t constants;
  rsa_3072_int_t encodedMessage;
  hardened_bool_t result;

  // Encode message
  hmac_error_t err =
      rsa_3072_encode_sha256(testvec->msg, testvec->msgLen, &encodedMessage);
  if (err != kHmacOk) {
    LOG_ERROR("Error from HMAC during message encoding: 0x%08x.", err);
    return false;
  }

  // Precompute Montgomery constants
  otbn_error_t err = rsa_3072_compute_constants(&testvec->publicKey, &constants);
  if (err != kOtbnOk) {
    LOG_ERROR("Error from OTBN while computing constants: 0x%08x.", err);
    return false;
  }

  // Attempt to verify signature
  err = rsa_3072_verify(&testvec->signature, &encodedMessage,
                                  &testvec->publicKey, &constants, &result);
  if (err != kOtbnOk) {
    LOG_ERROR("Error from OTBN during signature verification: 0x%08x.", err);
    return false;
  }

  if (testvec->valid) {
    CHECK(result == kHardenedBoolTrue);
  } else {
    CHECK(result == kHardenedBoolFalse);
  }

  return true;
}

const test_config_t kTestConfig;

bool test_main(void) {
  // Stays true only if all tests pass.
  bool result = true;

  entropy_testutils_boot_mode_init();

  for (uint32_t i = 0; i < RSA_3072_VERIFY_NUM_TESTS; i++) {
    LOG_INFO("Starting rsa_3072_verify_test on test vector %d of %d...", i + 1,
             RSA_3072_VERIFY_NUM_TESTS);
    rsa_3072_verify_test_vector_t testvec = rsa_3072_verify_tests[i];
    bool local_result = rsa_3072_verify_test(&testvec);
    if (local_result) {
      LOG_INFO("Finished rsa_3072_verify_test on test vector %d : ok", i + 1);
    } else {
      LOG_ERROR(
          "Finished rsa_3072_verify_test on test vector %d : error",
          i + 1);
      LOG_INFO("Test notes: %s", testvec.comment);
    }
    result &= local_result;
  }

  return result;
}
