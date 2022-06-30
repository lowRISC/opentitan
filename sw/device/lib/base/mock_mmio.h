// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_MOCK_MMIO_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_MOCK_MMIO_H_

#include <initializer_list>
#include <memory>
#include <random>
#include <stdint.h>
#include <string.h>
#include <vector>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio_test_utils.h"

namespace mock_mmio {
/**
 * Reads a little-endian integer from `bytes`. This function is lazy, and will
 * only perform the converion when used with an EXPECT_* macro. For example:
 *   EXPECT_READ32(offset, LeInt("abcd"));
 *
 * It is not possible to directly pass in string literals into EXPECT_* macros;
 * this is a limitation of C++'s implicit conversion rules and overload
 * resolution order.
 */
inline mock_mmio::LittleEndianBytes LeInt(const char *bytes) { return {bytes}; }

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
      .WillOnce(testing::Return(mock_mmio::ToInt<uint8_t>(__VA_ARGS__)))

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
      .WillOnce(testing::Return(mock_mmio::ToInt<uint32_t>(__VA_ARGS__)))

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
  EXPECT_CALL(dev, Write8(offset, mock_mmio::ToInt<uint8_t>(__VA_ARGS__)))

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
  EXPECT_CALL(dev, Write32(offset, mock_mmio::ToInt<uint32_t>(__VA_ARGS__)))

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
 * Expect a shadowed write to the given offset with the given 8-bit value.
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
#define EXPECT_WRITE8_SHADOWED(offset, ...) \
  EXPECT_WRITE8(offset, __VA_ARGS__);       \
  EXPECT_WRITE8(offset, __VA_ARGS__);

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

/**
 * Expect a shadowed write to the given offset with the given 32-bit value.
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
#define EXPECT_WRITE32_SHADOWED(offset, ...) \
  EXPECT_WRITE32(offset, __VA_ARGS__);       \
  EXPECT_WRITE32(offset, __VA_ARGS__);

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

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_MOCK_MMIO_H_
