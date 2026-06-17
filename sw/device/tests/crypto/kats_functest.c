// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <string.h>

#include "sw/device/lib/crypto/impl/kats.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

OTTF_DEFINE_TEST_CONFIG();

static otcrypto_state_t test_cryptolib_state = {0};

status_t test_run_kats(void) {
#ifdef FIPS_MODE
  LOG_INFO("Testing run_kats with kTestLastBit...");

  // 1. Test out-of-bounds flag (>= 1UL << kTestLastBit)
  kat_id_t oob_id = {.flags = 1UL << kTestLastBit};
  otcrypto_status_t status = run_kats(oob_id);
  TRY_CHECK(status.value != kHardenedBoolTrue,
            "Expected failure for out of bounds test flags.");

  // 2. Test running all KATs
  LOG_INFO("Running all KATs...");
  status = run_kats(OTCRYPTO_KAT_ALL_TESTS);
  TRY_CHECK(status.value == kHardenedBoolTrue,
            "Expected success for running all KATs.");

  LOG_INFO("run_kats verified successfully.");
#endif

  return OK_STATUS();
}

bool test_main(void) {
  CHECK_STATUS_OK(
      otcrypto_init(kOtcryptoKeySecurityLevelHigh, &test_cryptolib_state));

  CHECK_STATUS_OK(test_run_kats());

  return true;
}
