// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_MOCK_CRC32_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_MOCK_CRC32_H_

#include "sw/device/lib/base/crc32.h"
#include "sw/device/lib/base/global_mock.h"

namespace rom_test {
namespace internal {

/**
 * Mock class for crc32.
 */
class MockCrc32 : public global_mock::GlobalMock<MockCrc32> {
 public:
  MOCK_METHOD(void, Init, (uint32_t *));
  MOCK_METHOD(void, Add8, (uint32_t *, uint8_t));
  MOCK_METHOD(void, Add32, (uint32_t *, uint32_t));
  MOCK_METHOD(void, Add, (uint32_t *, const void *, size_t));
  MOCK_METHOD(uint32_t, Finish, (const uint32_t *));
  MOCK_METHOD(uint32_t, Crc32, (const void *, size_t));
};

}  // namespace internal

using MockCrc32 = testing::StrictMock<internal::MockCrc32>;

}  // namespace rom_test

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_MOCK_CRC32_H_
