// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/csrng.h"
#include "sw/device/silicon_creator/lib/error.h"

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  LOG_INFO("Initializing entropy complex for CSRNG test...");
  CHECK_STATUS_OK(entropy_testutils_auto_mode_init());

  LOG_INFO("Running CSRNG Known Answer Test (KAT)...");
  CHECK(csrng_kat() == kErrorOk, "CSRNG KAT failed!");
  LOG_INFO("CSRNG KAT passed successfully.");

  LOG_INFO("Testing CSRNG live TRNG generation...");
  CHECK(csrng_enable() == kErrorOk, "csrng_enable failed");
  CHECK(csrng_instantiate() == kErrorOk, "csrng_instantiate failed");

  uint32_t words[8] = {0};
  CHECK(csrng_read_words(words, 8) == kErrorOk, "csrng_read_words failed");

  LOG_INFO("Generated words:");
  for (size_t i = 0; i < 8; ++i) {
    LOG_INFO("  words[%d] = 0x%08x", (int)i, words[i]);
  }

  // Ensure words are non-zero
  uint32_t non_zero_count = 0;
  for (size_t i = 0; i < 8; ++i) {
    if (words[i] != 0) {
      non_zero_count++;
    }
  }
  CHECK(non_zero_count > 0, "All generated words were zero");

  uint32_t r1 = 0, r2 = 0;
  CHECK(csrng_read_words(&r1, 1) == kErrorOk, "csrng_read_words 1 failed");
  CHECK(csrng_read_words(&r2, 1) == kErrorOk, "csrng_read_words 2 failed");
  LOG_INFO("  r1 = 0x%08x, r2 = 0x%08x", r1, r2);

  LOG_INFO("CSRNG direct driver test passed successfully!");
  return true;
}
