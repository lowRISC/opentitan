// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BASE_MOCK_ABS_MMIO_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BASE_MOCK_ABS_MMIO_H_

#include "sw/device/lib/base/testing/mock_mmio_test_utils.h"
#include "sw/device/lib/testing/mask_rom_test.h"
#include "sw/device/silicon_creator/lib/base/abs_mmio.h"

namespace mask_rom_test {
namespace internal {
/**
 * Mock class for abs_mmio.c.
 */
class MockAbsMmio {
 public:
  MOCK_METHOD(uint32_t, Read8, (uint32_t addr));
  MOCK_METHOD(void, Write8, (uint32_t addr, uint32_t value));
  MOCK_METHOD(uint32_t, Read32, (uint32_t addr));
  MOCK_METHOD(void, Write32, (uint32_t addr, uint32_t value));

  virtual ~MockAbsMmio() {}
};
}  // namespace internal

using MockAbsMmio = GlobalMock<testing::StrictMock<internal::MockAbsMmio>>;

/**
 * Expect a read to the device `dev` at the given offset, returning the given
 * 8-bit value.
 *
 * The value may be given as an integer, a pointer to little-endian data,
 * or a `std::initializer_list<BitField>`.
 *
 * This expectation is sequenced with all other `EXPECT_READ` and `EXPECT_WRITE`
 * calls.
 */
#define EXPECT_ABS_READ8(mmio, addr, ...) \
  EXPECT_CALL(mmio, Read8(addr))          \
      .WillOnce(testing::Return(mock_mmio::ToInt<uint8_t>(__VA_ARGS__)))

/**
 * Expect a write to the given offset with the given 8-bit value.
 *
 * The value may be given as an integer, a pointer to little-endian data,
 * or a `std::initializer_list<BitField>`.
 *
 * This function is only available in tests using a fixture that derives
 * `MmioTest`.
 *
 * This expectation is sequenced with all other `EXPECT_READ` and `EXPECT_WRITE`
 * calls.
 */
#define EXPECT_ABS_WRITE8(mmio, addr, ...) \
  EXPECT_CALL(mmio, Write8(addr, mock_mmio::ToInt<uint8_t>(__VA_ARGS__)));

/**
 * Expect a read to the device `dev` at the given offset, returning the given
 * 32-bit value.
 *
 * The value may be given as an integer, a pointer to little-endian data,
 * or a `std::initializer_list<BitField>`.
 *
 * This expectation is sequenced with all other `EXPECT_READ` and `EXPECT_WRITE`
 * calls.
 */
#define EXPECT_ABS_READ32(mmio, addr, ...) \
  EXPECT_CALL(mmio, Read32(addr))          \
      .WillOnce(testing::Return(mock_mmio::ToInt<uint32_t>(__VA_ARGS__)))

/**
 * Expect a write to the given offset with the given 32-bit value.
 *
 * The value may be given as an integer, a pointer to little-endian data,
 * or a `std::initializer_list<BitField>`.
 *
 * This function is only available in tests using a fixture that derives
 * `MmioTest`.
 *
 * This expectation is sequenced with all other `EXPECT_READ` and `EXPECT_WRITE`
 * calls.
 */
#define EXPECT_ABS_WRITE32(mmio, addr, ...) \
  EXPECT_CALL(mmio, Write32(addr, mock_mmio::ToInt<uint32_t>(__VA_ARGS__)));

extern "C" {

uint32_t abs_mmio_read8(uint32_t addr) {
  return MockAbsMmio::Instance().Read8(addr);
}

void abs_mmio_write8(uint32_t addr, uint32_t value) {
  return MockAbsMmio::Instance().Write8(addr, value);
}

uint32_t abs_mmio_read32(uint32_t addr) {
  return MockAbsMmio::Instance().Read32(addr);
}

void abs_mmio_write32(uint32_t addr, uint32_t value) {
  return MockAbsMmio::Instance().Write32(addr, value);
}

}  // extern "C"
}  // namespace mask_rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BASE_MOCK_ABS_MMIO_H_
