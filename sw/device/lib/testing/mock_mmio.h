// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_MOCK_MMIO_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_MOCK_MMIO_H_

#include <stdint.h>
#include <string.h>

#include <initializer_list>
#include <memory>
#include <random>
#include <vector>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"

namespace mock_mmio {
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
 * Represents a single bit field in an integer, similar to BitField. It can be
 * used in most places that need a BitField, as well as in `EXPECT_MASK` macros.
 *
 * Like with BitFields, we can express the integer 0b0000'0000'1100'0101 as a
 * list of BitFieldMasks:
 *   {{0x0, 0x1, 1}, {0x1, 0x1, 0}, {0x2, 0x1, 1}, {0x3, 0x1, 0},
 *    {0x4, 0xff, 12}}
 *
 * In addition to showing how the integer is broken up, it also expresses
 * the lengths of fields, so it is clear that 0x0 and 0x2 are one-bit fields.
 * This also allows us to formally express that the fields 0x1 and 0x3 are
 * *unset*.
 *
 * In practice, this might use generated register constants, and look like
 *   {{FIELD_FOO_OFFSET, FIELD_FOO_MASK, 1}, ...}
 */
struct MaskedBitField {
  uintptr_t offset;
  uintptr_t mask;
  uintptr_t value;
};

namespace internal {
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
 *
 * @param fields a list of bit field entries.
 * @return a value of type `Int` built out of `fields`.
 */
template <typename Int>
Int ToInt(std::initializer_list<BitField> fields) {
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

/**
 * Reads a little-endian integer from `bytes`. This function is lazy, and will
 * only perform the converion when used with an EXPECT_* macro. For example:
 *   EXPECT_READ32(offset, LeInt("abcd"));
 *
 * It is not possible to directly pass in string literals into EXPECT_* macros;
 * this is a limitation of C++'s implicit conversion rules and overload
 * resolution order.
 */
inline internal::LittleEndianBytes LeInt(const char *bytes) { return {bytes}; }

/**
 * A MockDevice represents a mock implementation of an MMIO device.
 *
 * MockDevice provides two mockable member functions, representing a read and a
 * write at a particular offset from the base address. This class can be
 * converted into a `mmio_region_t` value, which, when used in `mmio.h`
 * functions like `read32()`, will map to the appropriate mock member function
 * calls.
 *
 * To maintain sequencing, `ReadN()` and `WriteN()` should not be
 * `EXPECT_CALL`'ed directly; instead, `EXPECT_READN` and `EXPECT_WRITEN` should
 * be used, instead.
 *
 * To use this class, `-DMOCK_MMIO` must be enabled in all translation units
 * using `mmio.h`.
 */
class MockDevice {
 public:
  MockDevice() = default;

  MockDevice(const MockDevice &) = delete;
  MockDevice &operator=(const MockDevice &) = delete;
  MockDevice(MockDevice &&) = delete;
  MockDevice &operator=(MockDevice &&) = delete;

  /**
   * Converts this MockDevice into a mmio_region_t opaque object,
   * which is compatible with `mmio.h` functions.
   */
  mmio_region_t region() { return {this}; }

  MOCK_METHOD(uint8_t, Read8, (ptrdiff_t offset));
  MOCK_METHOD(uint32_t, Read32, (ptrdiff_t offset));

  MOCK_METHOD(void, Write8, (ptrdiff_t offset, uint8_t value));
  MOCK_METHOD(void, Write32, (ptrdiff_t offset, uint32_t value));

  /**
   * Generates "garbage memory" for use in tests. This function should not
   * be called directly.
   */
  template <typename Int>
  Int GarbageMemory() {
    return std::uniform_int_distribution<Int>()(gen_);
  }

 private:
  static std::random_device rd;
  std::mt19937 gen_ = std::mt19937(rd());
};

/**
 * Conveninence fixture for creating device tests.
 *
 * This class should be derived by a test fixture (along with `testing::Test`)
 * and used in a `TEST_F` block. Doing so will make the `EXPECT_READN` and
 * `EXPECT_WRITEN` conveinence macros useable.
 *
 * The device being mocked can be accessed in the test body with `this->dev()`.
 * `this->` is required in this case, since the name `dev` is not immediately
 * visible.
 */
class MmioTest {
 protected:
  MockDevice &dev() { return *dev_; }

 private:
  std::unique_ptr<MockDevice> dev_ =
      std::make_unique<testing::StrictMock<MockDevice>>();
  testing::InSequence seq_;
};
}  // namespace mock_mmio

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
#define EXPECT_READ8_AT(dev, offset, ...) \
  EXPECT_CALL(dev, Read8(offset))         \
      .WillOnce(                          \
          testing::Return(mock_mmio::internal::ToInt<uint8_t>(__VA_ARGS__)))

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
#define EXPECT_READ32_AT(dev, offset, ...) \
  EXPECT_CALL(dev, Read32(offset))         \
      .WillOnce(                           \
          testing::Return(mock_mmio::internal::ToInt<uint32_t>(__VA_ARGS__)))

/**
 * Expect a write to the device `dev` at the given offset with the given 8-bit
 * value.
 *
 * The value may be given as an integer, a pointer to little-endian data,
 * or a `std::initializer_list<BitField>`.
 *
 * This expectation is sequenced with all other `EXPECT_READ` and `EXPECT_WRITE`
 * calls.
 */
#define EXPECT_WRITE8_AT(dev, offset, ...) \
  EXPECT_CALL(                             \
      dev, Write8(offset, mock_mmio::internal::ToInt<uint8_t>(__VA_ARGS__)))

/**
 * Expect a write to the device `dev` at the given offset with the given 32-bit
 * value.
 *
 * The value may be given as an integer, a pointer to little-endian data,
 * or a `std::initializer_list<BitField>`.
 *
 * This expectation is sequenced with all other `EXPECT_READ` and `EXPECT_WRITE`
 * calls.
 */
#define EXPECT_WRITE32_AT(dev, offset, ...) \
  EXPECT_CALL(                              \
      dev, Write32(offset, mock_mmio::internal::ToInt<uint32_t>(__VA_ARGS__)))

/**
 * Expect a read at the given offset, returning the given 8-bit value.
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
#define EXPECT_READ8(offset, ...) \
  EXPECT_READ8_AT(this->dev(), offset, __VA_ARGS__)

/**
 * Expect a read at the given offset, returning the given 32-bit value.
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
#define EXPECT_READ32(offset, ...) \
  EXPECT_READ32_AT(this->dev(), offset, __VA_ARGS__)

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
#define EXPECT_WRITE8(offset, ...) \
  EXPECT_WRITE8_AT(this->dev(), offset, __VA_ARGS__);

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
#define EXPECT_WRITE32(offset, ...) \
  EXPECT_WRITE32_AT(this->dev(), offset, __VA_ARGS__);

#define EXPECT_MASK_INTERNAL_(width, dev, off, ...)                        \
  do {                                                                     \
    auto &device = dev;                                                    \
    std::initializer_list<mock_mmio::MaskedBitField> fields = __VA_ARGS__; \
                                                                           \
    using Int = uint##width##_t;                                           \
    auto val = device.GarbageMemory<Int>();                                \
    EXPECT_READ##width##_AT(device, off, val);                             \
                                                                           \
    for (auto field : fields) {                                            \
      ASSERT_LT(field.offset, sizeof(Int) * 8);                            \
      ASSERT_LE(field.mask, std::numeric_limits<Int>::max());              \
      ASSERT_LE(field.value, field.mask);                                  \
                                                                           \
      val &= ~static_cast<Int>(field.mask << field.offset);                \
      val |= static_cast<Int>(field.value << field.offset);                \
    }                                                                      \
    EXPECT_WRITE##width##_AT(device, off, val);                            \
  } while (false)

/**
 * Expect an unspecified 8-bit read at the given offset, followed by a write to
 * the same location, with the same value but with some bits changed; the
 * remaining bits must be untouched.
 *
 * The changed bits are specified by a `std::initializer_list<MaskedBitField>`.
 *
 * This function is only available in tests using a fixture that derives
 * `MmioTest`.
 *
 * This expectation is sequenced with all other `EXPECT_READ` and `EXPECT_WRITE`
 * calls.
 */
#define EXPECT_MASK8(offset, ...) \
  EXPECT_MASK_INTERNAL_(8, this->dev(), offset, __VA_ARGS__)

/**
 * Expect an unspecified 32-bit read at the given offset, followed by a write to
 * the same location, with the same value but with some bits changed; the
 * remaining bits must be untouched.
 *
 * The changed bits are specified by a `std::initializer_list<MaskedBitField>`.
 *
 * This function is only available in tests using a fixture that derives
 * `MmioTest`.
 *
 * This expectation is sequenced with all other `EXPECT_READ` and `EXPECT_WRITE`
 * calls.
 */
#define EXPECT_MASK32(offset, ...) \
  EXPECT_MASK_INTERNAL_(32, this->dev(), offset, __VA_ARGS__)

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_MOCK_MMIO_H_
