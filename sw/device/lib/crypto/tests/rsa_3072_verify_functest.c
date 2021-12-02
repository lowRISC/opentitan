// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/silicon_creator/lib/crypto/rsa_3072/rsa_3072_verify.h"
#include "sw/device/silicon_creator/lib/crypto/tests/rsa_3072_verify_testvectors.h"
#include "sw/device/silicon_creator/lib/drivers/otbn.h"
#include "sw/device/silicon_creator/lib/test_main.h"

rom_error_t rsa_3072_verify_test(const rsa_3072_verify_test_vector_t *testvec) {
  rsa_3072_constants_t constants;
  rsa_3072_int_t encodedMessage;
  hardened_bool_t result;

  // Encode message
  RETURN_IF_ERROR(
      rsa_3072_encode_sha256(testvec->msg, testvec->msgLen, &encodedMessage));

  // Precompute Montgomery constants
  FOLD_OTBN_ERROR(rsa_3072_compute_constants(&testvec->publicKey, &constants));

  // Attempt to verify signature
  FOLD_OTBN_ERROR(rsa_3072_verify(&testvec->signature, &encodedMessage,
                                  &testvec->publicKey, &constants, &result));

  if (testvec->valid) {
    CHECK(result == kHardenedBoolTrue);
  } else {
    CHECK(result == kHardenedBoolFalse);
  }

  return kErrorOk;
}

const test_config_t kTestConfig;

bool test_main(void) {
  rom_error_t result = kErrorOk;

  entropy_testutils_boot_mode_init();

  for (uint32_t i = 0; i < RSA_3072_VERIFY_NUM_TESTS; i++) {
    LOG_INFO("Starting rsa_3072_verify_test on test vector %d of %d...", i + 1,
             RSA_3072_VERIFY_NUM_TESTS);
    rsa_3072_verify_test_vector_t testvec = rsa_3072_verify_tests[i];
    rom_error_t localErr = rsa_3072_verify_test(&testvec);
    if (localErr == kErrorOk) {
      LOG_INFO("Finished rsa_3072_verify_test on test vector %d : ok", i + 1);
    } else {
      LOG_ERROR(
          "Finished rsa_3072_verify_test on test vector %d : error 0x%08x.",
          i + 1, localErr);
      LOG_INFO("Test notes: %s", testvec.comment);
      result = localErr;
    }
  }

  return result == kErrorOk;
}
