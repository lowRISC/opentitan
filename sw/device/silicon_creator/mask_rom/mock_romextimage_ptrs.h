// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_MOCK_ROMEXTIMAGE_PTRS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_MOCK_ROMEXTIMAGE_PTRS_H_

#include "sw/device/lib/testing/mask_rom_test.h"
#include "sw/device/silicon_creator/mask_rom/romextimage_ptrs.h"

namespace mask_rom_test {
namespace internal {

/**
 * Mock class for romextimage_ptrs.h
 */
class MockRomextimagePtrs {
 public:
  MOCK_METHOD(const manifest_t *, slot_a_manifest_ptr_get, ());
  MOCK_METHOD(const manifest_t *, slot_b_manifest_ptr_get, ());

  virtual ~MockRomextimagePtrs() {}
};

}  // namespace internal

using MockRomextimagePtrs =
    GlobalMock<testing::StrictMock<internal::MockRomextimagePtrs>>;

extern "C" {

const manifest_t *romextimage_slot_a_manifest_ptr_get() {
  return MockRomextimagePtrs::Instance().slot_a_manifest_ptr_get();
}

const manifest_t *romextimage_slot_b_manifest_ptr_get() {
  return MockRomextimagePtrs::Instance().slot_b_manifest_ptr_get();
}

}  // extern "C"
}  // namespace mask_rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_MOCK_ROMEXTIMAGE_PTRS_H_
