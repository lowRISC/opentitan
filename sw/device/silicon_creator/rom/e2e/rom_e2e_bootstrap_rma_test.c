// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  uint32_t bitfield = retention_sram_get()->creator.reset_reasons;
  LOG_INFO("reset_info_bitfield: 0x%x", bitfield);
  return true;
}
