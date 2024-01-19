// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/silicon_creator/lib/crc32.h"

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  uint8_t buf[4096];
  for (size_t i = 0; i < ARRAYSIZE(buf); ++i) {
    buf[i] = i & UINT8_MAX;
  }

  const size_t kNumRepetitions = 10;
  for (size_t i = 0; i < kNumRepetitions; ++i) {
    const uint64_t start_cycles = ibex_mcycle_read();
    const uint32_t checksum = crc32(buf, sizeof(buf));
    const uint64_t end_cycles = ibex_mcycle_read();
    const uint64_t num_cycles = end_cycles - start_cycles;

    CHECK(num_cycles <= UINT32_MAX);
    const uint32_t num_cycles_u32 = (uint32_t)num_cycles;
    LOG_INFO("CRC32 computed in %d cycles.", num_cycles_u32);

    const uint32_t kExpectedChecksum = 0xa2912082;
    if (checksum != kExpectedChecksum) {
      LOG_ERROR("Checksum did not match. Expected %x, but got %x.",
                kExpectedChecksum, checksum);
      return false;
    }
  }
  return true;
}
