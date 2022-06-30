// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_MOCK_MMIO_TEST_UTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_MOCK_MMIO_TEST_UTILS_H_

#include <initializer_list>
#include <memory>
#include <random>
#include <stdint.h>
#include <string.h>
#include <vector>

#include "gmock/gmock.h"
#include "gtest/gtest.h"

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
}  // namespace mock_mmio

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_MOCK_MMIO_TEST_UTILS_H_
