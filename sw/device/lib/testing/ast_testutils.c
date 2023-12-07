// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include "sw/device/lib/testing/ast_testutils.h"

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/abs_mmio.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static const uint32_t kAstInit[] = {
  0xfd4a5a69,
  0xdce72194,
  0xb414038a,
  0xb800358d,
  0x34000089,
  0x380005d9,
  0x800005fc,
  0x10c607bc,
};

void ast_testutils_init(void) {
  for (size_t i = 0; i < ARRAYSIZE(kAstInit); ++i) {
    abs_mmio_write32(TOP_EARLGREY_AST_BASE_ADDR + i * sizeof(uint32_t), kAstInit[i]);
  }
}

