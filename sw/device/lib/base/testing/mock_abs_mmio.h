// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_TESTING_MOCK_ABS_MMIO_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_TESTING_MOCK_ABS_MMIO_H_

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/testing/global_mock.h"
#include "sw/device/lib/base/testing/mock_mmio_test_utils.h"
#include "sw/device/silicon_creator/testing/mask_rom_test.h"

namespace mask_rom_test {
namespace internal {
/**
 * Mock class for abs_mmio.c.
 */
class MockAbsMmio : public global_mock::GlobalMock<MockAbsMmio> {
 public:
  MOCK_METHOD(uint8_t, Read8, (uint32_t addr));
  MOCK_METHOD(void, Write8, (uint32_t addr, uint8_t value));
  MOCK_METHOD(void, Write8Shadowed, (uint32_t addr, uint8_t value));
  MOCK_METHOD(uint32_t, Read32, (uint32_t addr));
  MOCK_METHOD(void, Write32, (uint32_t addr, uint32_t value));
  MOCK_METHOD(void, Write32Shadowed, (uint32_t addr, uint32_t value));
};
}  // namespace internal

using MockAbsMmio = testing::StrictMock<internal::MockAbsMmio>;

/**
 * Expect an abs_mmio read at the given address, returning the given 8-bit
 * value.
 *
 * @param addr Read address.
 * @param ... Value to return. May be an integer, a pointer to little-endian
 * data, or a `std::initializer_list<BitField>`.
 */
#define EXPECT_ABS_READ8(addr, ...)                                  \
  EXPECT_CALL(::mask_rom_test::MockAbsMmio::Instance(), Read8(addr)) \
      .WillOnce(testing::Return(mock_mmio::ToInt<uint8_t>(__VA_ARGS__)))

/**
 * Expect an abs_mmio write to the given address with the given 8-bit value.
 *
 * @param addr Write address.
 * @param ... Expected value to be written. May be an integer, a pointer to
 * little-endian data, or a `std::initializer_list<BitField>`.
 */
#define EXPECT_ABS_WRITE8(addr, ...)                    \
  EXPECT_CALL(::mask_rom_test::MockAbsMmio::Instance(), \
              Write8(addr, mock_mmio::ToInt<uint8_t>(__VA_ARGS__)));

/**
 * Expect a shadowed abs_mmio write to the given address with the given 8-bit
 * value.
 *
 * @param addr Write address.
 * @param ... Expected value to be written. May be an integer, a pointer to
 * little-endian data, or a `std::initializer_list<BitField>`.
 */
#define EXPECT_ABS_WRITE8_SHADOWED(addr, ...)           \
  EXPECT_CALL(::mask_rom_test::MockAbsMmio::Instance(), \
              Write8Shadowed(addr, mock_mmio::ToInt<uint8_t>(__VA_ARGS__)));

/**
 * Expect an abs_mmio read at the given address, returning the given 32-bit
 * value.
 *
 * @param addr Read address.
 * @param ... Value to return. May be an integer, a pointer to little-endian
 * data, or a `std::initializer_list<BitField>`.
 */
#define EXPECT_ABS_READ32(addr, ...)                                  \
  EXPECT_CALL(::mask_rom_test::MockAbsMmio::Instance(), Read32(addr)) \
      .WillOnce(testing::Return(mock_mmio::ToInt<uint32_t>(__VA_ARGS__)))

/**
 * Expect an abs_mmio write to the given address with the given 32-bit value.
 *
 * @param addr Write address.
 * @param ... Expected value to be written. May be an integer, a pointer to
 * little-endian data, or a `std::initializer_list<BitField>`.
 */
#define EXPECT_ABS_WRITE32(addr, ...)                   \
  EXPECT_CALL(::mask_rom_test::MockAbsMmio::Instance(), \
              Write32(addr, mock_mmio::ToInt<uint32_t>(__VA_ARGS__)));

/**
 * Expect a shadowed abs_mmio write to the given address with the given 32-bit
 * value.
 *
 * @param addr Write address.
 * @param ... Expected value to be written. May be an integer, a pointer to
 * little-endian data, or a `std::initializer_list<BitField>`.
 */
#define EXPECT_ABS_WRITE32_SHADOWED(addr, ...)          \
  EXPECT_CALL(::mask_rom_test::MockAbsMmio::Instance(), \
              Write32Shadowed(addr, mock_mmio::ToInt<uint32_t>(__VA_ARGS__)));

extern "C" {

uint8_t abs_mmio_read8(uint32_t addr) {
  return MockAbsMmio::Instance().Read8(addr);
}

void abs_mmio_write8(uint32_t addr, uint8_t value) {
  MockAbsMmio::Instance().Write8(addr, value);
}

void abs_mmio_write8_shadowed(uint32_t addr, uint8_t value) {
  MockAbsMmio::Instance().Write8Shadowed(addr, value);
}

uint32_t abs_mmio_read32(uint32_t addr) {
  return MockAbsMmio::Instance().Read32(addr);
}

void abs_mmio_write32(uint32_t addr, uint32_t value) {
  MockAbsMmio::Instance().Write32(addr, value);
}

void abs_mmio_write32_shadowed(uint32_t addr, uint32_t value) {
  MockAbsMmio::Instance().Write32Shadowed(addr, value);
}

}  // extern "C"
}  // namespace mask_rom_test

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_TESTING_MOCK_ABS_MMIO_H_
