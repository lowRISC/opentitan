// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/test_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static rom_error_t retention_sram_clear_test(void) {
  // Set every bit in the retention SRAM to one.
  // Note: memset cannot be used directly because it discards the volatile
  // qualifier.
  volatile retention_sram_t *ret = retention_sram_get();
  retention_sram_t ones;
  memset(&ones, 0xff, sizeof(retention_sram_t));
  *ret = ones;

  // Clear the retention SRAM (set every bit to zero).
  retention_sram_clear();

  // Check that the retention SRAM was fully cleared.
  // Note: memcmp cannot be used directly because it discards the volatile
  // qualifier.
  retention_sram_t zeros;
  memset(&zeros, 0, sizeof(retention_sram_t));
  retention_sram_t result = *ret;
  if (memcmp(&zeros, &result, sizeof(retention_sram_t)) != 0) {
    LOG_ERROR("Retention SRAM not cleared.");
    return kErrorUnknown;  // Unreachable.
  }
  return kErrorOk;
}

const test_config_t kTestConfig;

bool test_main(void) {
  rom_error_t result = kErrorOk;
  EXECUTE_TEST(result, retention_sram_clear_test);
  return result == kErrorOk;
}
