// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_MOCK_SIGVERIFY_KEYS_PTRS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_MOCK_SIGVERIFY_KEYS_PTRS_H_

#include "sw/device/lib/base/global_mock.h"
#include "sw/device/silicon_creator/rom/sigverify_keys_ptrs.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace rom_test {
namespace internal {

/**
 * Mock class for sigverify_keys_ptrs.h
 */
class MockSigverifyKeysPtrs
    : public global_mock::GlobalMock<MockSigverifyKeysPtrs> {
 public:
  MOCK_METHOD(const sigverify_rom_key_t *, RsaKeysGet, ());
  MOCK_METHOD(size_t, RsaKeysCntGet, ());
  MOCK_METHOD(size_t, RsaKeysStepGet, ());
};

}  // namespace internal

using MockSigverifyKeysPtrs =
    testing::StrictMock<internal::MockSigverifyKeysPtrs>;

}  // namespace rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_MOCK_SIGVERIFY_KEYS_PTRS_H_
