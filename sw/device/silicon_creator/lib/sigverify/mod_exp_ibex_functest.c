// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/sigverify/mod_exp_ibex.h"
#include "sw/device/silicon_creator/lib/sigverify/sigverify_tests/sigverify_testvectors.h"
#include "sw/device/silicon_creator/lib/test_main.h"

// Index of the test vector currently under test
static uint32_t test_index;

rom_error_t sigverify_mod_exp_ibex_test(void) {
  sigverify_test_vector_t testvec = sigverify_tests[test_index];

  sigverify_rsa_buffer_t recovered_message;
  rom_error_t err =
      sigverify_mod_exp_ibex(&testvec.key, &testvec.sig, &recovered_message);
  if (err != kErrorOk) {
    if (testvec.valid) {
      LOG_ERROR("Error on a valid signature.");
      LOG_INFO("Test notes: %s", testvec.comment);
      return err;
    } else {
      // If a test vector is marked invalid, it's okay to return an error
      return kErrorOk;
    }
  }

  bool passed = memcmp(testvec.encoded_msg, recovered_message.data,
                       sizeof(testvec.encoded_msg)) == 0;
  if (testvec.valid && !passed) {
    // Signature verification failed when it was expected to pass.
    LOG_ERROR("Failed to verify a valid signature.");
    LOG_INFO("Test notes: %s", testvec.comment);
    return kErrorUnknown;
  } else if (!testvec.valid && passed) {
    // Signature verification passed when it was expected to fail.
    LOG_ERROR("Invalid signature passed verification.");
    LOG_INFO("Test notes: %s", testvec.comment);
    return kErrorUnknown;
  }

  return kErrorOk;
}

const test_config_t kTestConfig;

bool test_main(void) {
  rom_error_t result = kErrorOk;

  for (uint32_t i = 0; i < SIGVERIFY_NUM_TESTS; i++) {
    LOG_INFO("Starting test vector %d of %d...", i + 1, SIGVERIFY_NUM_TESTS);
    test_index = i;
    EXECUTE_TEST(result, sigverify_mod_exp_ibex_test);
  }
  return result == kErrorOk;
}
