// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/test_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

rom_error_t retention_sram_test(void) {
  // Use 64-bit values for the retention RAM to reduce the probability of an
  // individual value staying the same after scrambling.
  volatile uint64_t *ret_ram =
      (volatile uint64_t *)TOP_EARLGREY_RAM_RET_AON_BASE_ADDR;
  size_t ret_ram_len = TOP_EARLGREY_RAM_RET_AON_SIZE_BYTES / sizeof(ret_ram[0]);

  // Set the retention SRAM to known values.
  LOG_INFO("Initializing retention SRAM.");
  for (size_t i = 0; i < ret_ram_len; ++i) {
    ret_ram[i] = 0;
  }

  // Scramble the retention SRAM.
  LOG_INFO("Scrambling retention SRAM.");
  if (retention_sram_scramble() != kErrorOk) {
    LOG_ERROR("Scrambling failed.");
    return kErrorUnknown;
  }

  // Check that every entry in the retention SRAM has changed.
  // Retention SRAM accesses will stall until scrambling is complete.
  uint32_t matches = 0;
  LOG_INFO(
      "Checking retention SRAM is scrambled (will stall for a short time).");
  for (size_t i = 0; i < ret_ram_len; ++i) {
    if (ret_ram[i] == 0) {
      LOG_ERROR("Retention SRAM potentially unscrambled at %p.", &ret_ram[i]);
      matches += 1;
    }
  }

  // It is possible that scrambling executed correctly but one or more double
  // words still match. If this occurs in practice it may be necessary to
  // increase the number of matches that are tolerated.
  LOG_INFO("Finishing retention SRAM scrambling test (matches=%u).", matches);
  return matches != 0 ? kErrorUnknown : kErrorOk;
}

const test_config_t kTestConfig;

bool test_main(void) {
  rom_error_t result = kErrorOk;
  EXECUTE_TEST(result, retention_sram_test);
  return result == kErrorOk;
}
