// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_MOCK_ROM_EXT_BOOT_POLICY_PTRS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_MOCK_ROM_EXT_BOOT_POLICY_PTRS_H_

#include "sw/device/lib/base/testing/global_mock.h"
#include "sw/device/silicon_creator/rom_ext/rom_ext_boot_policy_ptrs.h"
#include "sw/device/silicon_creator/testing/mask_rom_test.h"

namespace mask_rom_test {
namespace internal {

/**
 * Mock class for rom_ext_boot_policy_ptrs.h
 */
class MockRomExtBootPolicyPtrs
    : public global_mock::GlobalMock<MockRomExtBootPolicyPtrs> {
 public:
  MOCK_METHOD(const manifest_t *, ManifestA, ());
  MOCK_METHOD(const manifest_t *, ManifestB, ());
};

}  // namespace internal

using MockRomExtBootPolicyPtrs =
    testing::StrictMock<internal::MockRomExtBootPolicyPtrs>;

}  // namespace mask_rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_MOCK_ROM_EXT_BOOT_POLICY_PTRS_H_
