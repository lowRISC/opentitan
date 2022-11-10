// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/test_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

/**
 * Repeated pattern to fill the Retention RAM with
 */
enum {
  kPattern = 0xab,
};

// Variables of type `retention_sram_t` are static to reduce stack usage.
static retention_sram_t ret;
static uint64_t raw[sizeof(retention_sram_t) / sizeof(uint64_t) + 1];

rom_error_t retention_ram_init_test(void) {
  uint64_t pattern64;
  memset(&pattern64, kPattern, sizeof(pattern64));

  retention_sram_t *ret = retention_sram_get();
  uint32_t reset_reasons = ret->reset_reasons;

  // Verify that reset_reasons reports POR.
  if (bitfield_bit32_read(reset_reasons, kRstmgrReasonPowerOn)) {
    // This branch runs after the POR after initializing the testing environment
    LOG_INFO("Writing known pattern");
    memset(ret, kPattern, sizeof(retention_sram_t));

    LOG_INFO("Requesting SW reset");
    rstmgr_reset();
  } else if (bitfield_bit32_read(reset_reasons, kRstmgrReasonSoftwareRequest)) {
    // This branch runs after the SW-requested reset
    LOG_INFO("Ensuring all sections have changed");
    memcpy(raw, ret, sizeof(retention_sram_t));

    uint32_t matches = 0;
    for (size_t i = 0; i < ARRAYSIZE(raw); ++i) {
      if (raw[i] == pattern64) {
        LOG_ERROR("Retention SRAM unchanged at offset %u.", i);
        matches += 1;
      }
    }
    // It is possible, albeit extremely unlikely, that scrambling executed
    // correctly but one or more double words still match. If this occurs in
    // practice it may be necessary to increase the number of matches that are
    // tolerated.
    return matches == 0 ? kErrorOk : kErrorUnknown;
  }
  LOG_ERROR("Did not find a reset reason of POR or SW request");
  return kErrorUnknown;
}

bool test_main(void) {
  rom_error_t result = kErrorOk;
  EXECUTE_TEST(result, retention_ram_init_test);
  return result == kErrorOk;
}
