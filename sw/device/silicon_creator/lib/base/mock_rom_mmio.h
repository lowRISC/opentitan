// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BASE_MOCK_ROM_MMIO_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BASE_MOCK_ROM_MMIO_H_

#include "sw/device/lib/testing/mask_rom_test.h"
#include "sw/device/silicon_creator/lib/base/rom_mmio.h"

namespace mask_rom_test {
namespace internal {
/**
 * Mock class for mmio.c.
 */
class MockMmio {
 public:
  MOCK_METHOD(uint32_t, Read8, (uint32_t addr));
  MOCK_METHOD(void, Write8, (uint32_t addr, uint32_t value));
  MOCK_METHOD(uint32_t, Read32, (uint32_t addr));
  MOCK_METHOD(void, Write32, (uint32_t addr, uint32_t value));

  virtual ~MockMmio() {}

 protected:
  ::testing::InSequence seq_;
};

/**
 * Represents a single bit field in an integer, useable with EXPECT_* macros
 * defined in this file.
 *
 * An integer can be expressed as a list of BitField values, and can be more
 * convenient to use than 0b or 0x literals in some cases. For example, the
 * integer 0b0000'0000'1100'0101 could be expressed as
 *   {{0x0, 1}, {0x2, 1}, {0x4, 12}}
 * This form makes it clearer to the reader that 0x0, 0x2, and 04 are indices
 * to bitfields, which are set to particular values.
 *
 * In practice, this might use generated register constants, and look like
 *   {{FIELD_FOO_OFFSET, 1}, {FIELD_BAR_OFFSET, 1}, {FIELD_BAZ_OFFSET, 12}}
 *
 * This type does not specify the lengths of bitfields; MaskedBitField should be
 * used for that, instead.
 */
struct BitField {
  uintptr_t offset;
  uintptr_t value;
};

/**
 * Implicit conversion guard around `char *`. See `LeInt()`.
 */
struct LittleEndianBytes {
  const char *bytes;
};

/**
 * Converts the argument into an unsigned integer of type `Int`.
 *
 * This overload is simply the identity on integers, and allows integers to be
 * converted into themselves. This enables the basic EXPECT_* macros:
 *   EXPECT_READ32(offset, 0xcafecafe);
 *
 * @param val an integer.
 * @return the value `val`.
 */
template <typename Int>
Int ToInt(Int val) {
  return val;
}

/**
 * Converts the argument into an unsinged integer of type `Int`.
 *
 * This overload assumes that `str` is a valid pointer to a buffer of at least
 * `sizeof(Int)` bytes, which are memcpy'd out as an `Int`. This enables
 * memcpy-like EXPECT_* macros:
 *   EXPECT_READ32(offset, LeInt("rv32"));
 *   EXPECT_READ32(offset, LeInt("imc\0"));
 *
 * @param str a pointer to a valid buffer of length at least `sizeof(Int)`.
 * @return a value of type `Int` memcpy'd out of `str`.
 */
template <typename Int>
Int ToInt(LittleEndianBytes str) {
  Int val;
  memcpy(&val, str.bytes, sizeof(Int));
  return val;
}

/**
 * Converts the argument into an unsigned integer of type `Int`.
 *
 * This overload performs the shifts and ors described by `fields`. See
 * `BitField`'s documentation for details one what this means. This overload
 * enables bitfield EXPECT_* macros:
 *   EXPECT_READ32(offset, {{A_OFFSET, 0x55}, {B_OFFSET, 0xaa}});
 *   EXPECT_READ32(offset, fields);
 * where `fields` is an `std::vector<BitField>`.
 *
 * @param fields a list of bit field entries.
 * @return a value of type `Int` built out of `fields`.
 */
template <typename Int>
Int ToInt(std::vector<BitField> fields) {
  Int val = 0;
  for (auto field : fields) {
    // Due to the way that gtest ASSERT_* works, and the fact that this must be
    // a function (since we use function overloading), these cannot be ASSERTs,
    // and must be EXPECTs.
    EXPECT_LE(field.offset, sizeof(Int) * 8);
    val |= static_cast<Int>(field.value << field.offset);
  }
  return val;
}

}  // namespace internal

using MockMmio = GlobalMock<testing::StrictMock<internal::MockMmio>>;

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
#define EXPECT_MMIO_READ8(mmio, addr, ...) \
  EXPECT_CALL(mmio, Read8(addr))           \
      .WillOnce(testing::Return(           \
          mask_rom_test::internal::ToInt<uint8_t>(__VA_ARGS__)))

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
#define EXPECT_MMIO_WRITE8(mmio, addr, ...) \
  EXPECT_CALL(                              \
      mmio,                                 \
      Write8(addr, mask_rom_test::internal::ToInt<uint8_t>(__VA_ARGS__)));

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
#define EXPECT_MMIO_READ32(mmio, addr, ...) \
  EXPECT_CALL(mmio, Read32(addr))           \
      .WillOnce(testing::Return(            \
          mask_rom_test::internal::ToInt<uint32_t>(__VA_ARGS__)))

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
#define EXPECT_MMIO_WRITE32(mmio, addr, ...) \
  EXPECT_CALL(                               \
      mmio,                                  \
      Write32(addr, mask_rom_test::internal::ToInt<uint32_t>(__VA_ARGS__)));

extern "C" {

uint32_t rom_mmio_read8(uint32_t addr) {
  return MockMmio::Instance().Read8(addr);
}

void rom_mmio_write8(uint32_t addr, uint32_t value) {
  return MockMmio::Instance().Write8(addr, value);
}

uint32_t rom_mmio_read32(uint32_t addr) {
  return MockMmio::Instance().Read32(addr);
}

void rom_mmio_write32(uint32_t addr, uint32_t value) {
  return MockMmio::Instance().Write32(addr, value);
}

}  // extern "C"
}  // namespace mask_rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BASE_MOCK_ROM_MMIO_H_
