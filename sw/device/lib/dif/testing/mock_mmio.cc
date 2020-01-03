// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/testing/mock_mmio.h"

#include <cstdio>

using dif_test::AccessType;

extern "C" uint32_t reg32_read(reg32_t base, ptrdiff_t offset) {
  auto index = base->current_action_index;
  if (index >= base->expected_actions.size()) {
    std::printf("Attempted to execute superfluous read.\n");
    ++base->failed_expectations;
    ++base->current_action_index;
    return 0xffffffff;
  }

  auto expected = base->expected_actions[index];
  ++base->current_action_index;

  if (expected.kind == AccessType::kRead && expected.offset == offset) {
    return expected.value;
  }

  const char *type_name = expected.kind == AccessType::kRead ? "read" : "write";
  std::printf("Mismatch at action #%zu:\n", index);
  std::printf("* Expected: %s at 0x%.8tx, with value 0x%.8x.\n", type_name,
              expected.offset, expected.value);
  std::printf("* Got: read at 0x%.8tx.\n", offset);
  ++base->failed_expectations;

  return 0xffffffff;
}

extern "C" void reg32_write(reg32_t base, ptrdiff_t offset, uint32_t value) {
  auto index = base->current_action_index;
  if (index >= base->expected_actions.size()) {
    std::printf("Attempted to execute superfluous write.\n");
    ++base->failed_expectations;
    ++base->current_action_index;
    return;
  }

  auto expected = base->expected_actions[index];
  ++base->current_action_index;

  if (expected.kind == AccessType::kWrite && expected.offset == offset &&
      expected.value == value) {
    return;
  }

  const char *type_name = expected.kind == AccessType::kRead ? "read" : "write";
  std::printf("Mismatch at action #%zu:\n", index);
  std::printf("* Expected: %s at 0x%.8tx, with value 0x%.8x.\n", type_name,
              expected.offset, expected.value);
  std::printf("* Got: write at 0x%.8tx, with value 0x%.8x\n.", offset, value);
  ++base->failed_expectations;

  return;
}
