// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/silicon_creator/lib/drivers/rnd.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/test_main.h"

OTTF_DEFINE_TEST_CONFIG();

rom_error_t rnd_test(void) {
  const size_t kTestNumIter = 5;
  uint32_t prev = rnd_uint32();
  uint32_t error_cnt = 0;
  for (size_t i = 0; i < kTestNumIter; ++i) {
    uint32_t got = rnd_uint32();
    if (got == prev) {
      LOG_ERROR("Unexpected duplicate random number: 0x%x.", got);
      error_cnt += 1;
    }
    prev = got;
  }
  if (error_cnt > 0) {
    LOG_ERROR("rnd_test failed, expected: 0 errors, got: %d.", error_cnt);
    return kErrorUnknown;
  }
  return kErrorOk;
}

bool test_main(void) {
  rom_error_t result = kErrorOk;
  EXECUTE_TEST(result, rnd_test);
  return result == kErrorOk;
}
