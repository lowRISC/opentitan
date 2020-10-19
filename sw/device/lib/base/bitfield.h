// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_BITFIELD_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_BITFIELD_H_

#include <stdbool.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * @file
 * @brief Bitfield Manipulation Functions
 */

/**
 * All the bitfield functions are pure (they do not modify their arguments), so
 * the result must be used. We enable warnings to ensure this happens.
 */
#define BITFIELD_WARN_UNUSED_RESULT __attribute__((warn_unused_result))

/**
 * A field of a 32-bit bitfield.
 *
 * The following field definition: `{ .mask = 0b11, .index = 12 }`
 *
 * Denotes the X-marked bits in the following 32-bit bitfield:
 *
 *     field:  0b--------'--------'--XX----'--------
 *     index:   31                                 0
 *
 * Restrictions: The index plus the width of the mask must not be greater than
 * 31.
 */
typedef struct bitfield_field32 {
  /** The field mask. Usually all ones. */
  uint32_t mask;
  /** The field position in the bitfield, counting from the zero-bit. */
  uint32_t index;
} bitfield_field32_t;

/**
 * Reads a value from `field` in `bitfield`.
 *
 * This function uses the `field` parameter to read the value from `bitfield`.
 * The resulting value will be shifted right and zero-extended so the field's
 * zero-bit is the return value's zero-bit.
 *
 * @param bitfield Bitfield to get the field from.
 * @param field Field to read out from.
 * @return Zero-extended `field` from `bitfield`.
 */
BITFIELD_WARN_UNUSED_RESULT
inline uint32_t bitfield_field32_read(uint32_t bitfield,
                                      bitfield_field32_t field) {
  return (bitfield >> field.index) & field.mask;
}

/**
 * Writes `value` to `field` in `bitfield`.
 *
 * This function uses the `field` parameter to set specific bits in `bitfield`.
 * The relevant portion of `bitfield` is zeroed before the bits are set to
 * `value`.
 *
 * @param bitfield Bitfield to set the field in.
 * @param field Field within bitfield to be set.
 * @param value Value for the new field.
 * @return `bitfield` with `field` set to `value`.
 */
BITFIELD_WARN_UNUSED_RESULT
inline uint32_t bitfield_field32_write(uint32_t bitfield,
                                       bitfield_field32_t field,
                                       uint32_t value) {
  bitfield &= ~(field.mask << field.index);
  bitfield |= (value & field.mask) << field.index;
  return bitfield;
}

/**
 * A single bit in a 32-bit bitfield.
 *
 * This denotes the position of a single bit, counting from the zero-bit.
 *
 * For instance, `(bitfield_bit_index_t)4` denotes the X-marked bit in the
 * following 32-bit bitfield:
 *
 *     field:  0b--------'--------'--------'---X----
 *     index:   31                                 0
 *
 * Restrictions: The value must not be greater than 31.
 */
typedef uint32_t bitfield_bit32_index_t;

/**
 * Turns a `bitfield_bit32_index_t` into a `bitfield_field32_t` (which is more
 * general).
 *
 * @param bit_index The corresponding single bit to turn into a field.
 * @return A 1-bit field that corresponds to `bit_index`.
 */
BITFIELD_WARN_UNUSED_RESULT
inline bitfield_field32_t bitfield_bit32_to_field32(
    bitfield_bit32_index_t bit_index) {
  return (bitfield_field32_t){
      .mask = 0x1, .index = bit_index,
  };
}

/**
 * Reads the `bit_index`th bit in `bitfield`.
 *
 * @param bitfield Bitfield to get the bit from.
 * @param bit_index Bit to read.
 * @return `true` if the bit was one, `false` otherwise.
 */
BITFIELD_WARN_UNUSED_RESULT
inline bool bitfield_bit32_read(uint32_t bitfield,
                                bitfield_bit32_index_t bit_index) {
  return bitfield_field32_read(bitfield,
                               bitfield_bit32_to_field32(bit_index)) == 0x1u;
}

/**
 * Writes `value` to the `bit_index`th bit in `bitfield`.
 *
 * @param bitfield Bitfield to update the bit in.
 * @param bit_index Bit to update.
 * @param value Bit value to write to `bitfield`.
 * @return `bitfield` with the `bit_index`th bit set to `value`.
 */
BITFIELD_WARN_UNUSED_RESULT
inline uint32_t bitfield_bit32_write(uint32_t bitfield,
                                     bitfield_bit32_index_t bit_index,
                                     bool value) {
  return bitfield_field32_write(bitfield, bitfield_bit32_to_field32(bit_index),
                                value ? 0x1u : 0x0u);
}

/**
 * Find First Set Bit
 *
 * Returns one plus the index of the least-significant 1-bit of a 32-bit word.
 *
 * For instance, `bitfield_find_first_set32(field)` of the below 32-bit value
 * returns `5`.
 *
 *     field:  0b00000000'00000000'11111111'00010000
 *     index:   31                                 0
 *
 * This is the canonical definition for the GCC/Clang builtin `__builtin_ffs`,
 * and hence takes and returns a signed integer.
 *
 * @param bitfield Bitfield to find the first set bit in.
 * @return One plus the index of the least-significant 1-bit of `bitfield`.
 */
BITFIELD_WARN_UNUSED_RESULT
inline int32_t bitfield_find_first_set32(int32_t bitfield) {
  return __builtin_ffs(bitfield);
}

/**
 * Count Leading Zeroes
 *
 * Returns the number of leading 0-bits in `bitfield`, starting at the most
 * significant bit position. If `bitfield` is 0, the result is 32, to match the
 * RISC-V B Extension.
 *
 * For instance, `bitfield_count_leading_zeroes32(field)` of the below 32-bit
 * value returns `16`.
 *
 *     field:  0b00000000'00000000'11111111'00010000
 *     index:   31                                 0
 *
 * This is the canonical definition for the GCC/Clang builtin `__builtin_clz`,
 * and hence returns a signed integer.
 *
 * @param bitfield Bitfield to count leading 0-bits from.
 * @return The number of leading 0-bits in `bitfield`.
 */
BITFIELD_WARN_UNUSED_RESULT
inline int32_t bitfield_count_leading_zeroes32(uint32_t bitfield) {
  return (bitfield != 0) ? __builtin_clz(bitfield) : 32;
}

/**
 * Count Trailing Zeroes
 *
 * Returns the number of trailing 0-bits in `bitfield`, starting at the least
 * significant bit position. If `bitfield` is 0, the result is 32, to match the
 * RISC-V B Extension.
 *
 * For instance, `bitfield_count_trailing_zeroes32(field)` of the below 32-bit
 * value returns `4`.
 *
 *     field:  0b00000000'00000000'11111111'00010000
 *     index:   31                                 0
 *
 * This is the canonical definition for the GCC/Clang builtin `__builtin_ctz`,
 * and hence returns a signed integer.
 *
 * @param bitfield Bitfield to count trailing 0-bits from.
 * @return The number of trailing 0-bits in `bitfield`.
 */
BITFIELD_WARN_UNUSED_RESULT
inline int32_t bitfield_count_trailing_zeroes32(uint32_t bitfield) {
  return (bitfield != 0) ? __builtin_ctz(bitfield) : 32;
}

/**
 * Count Set Bits
 *
 * Returns the number of 1-bits in `bitfield`.
 *
 * For instance, `bitfield_popcount32(field)` of the below 32-bit value returns
 * `9`.
 *
 *     field:  0b00000000'00000000'11111111'00010000
 *     index:   31                                 0
 *
 * This is the canonical definition for the GCC/Clang builtin
 * `__builtin_popcount`, and hence returns a signed integer.
 *
 * @param bitfield Bitfield to count 1-bits from.
 * @return The number of 1-bits in `bitfield`.
 */
BITFIELD_WARN_UNUSED_RESULT
inline int32_t bitfield_popcount32(uint32_t bitfield) {
  return __builtin_popcount(bitfield);
}

/**
 * Parity
 *
 * Returns the number of 1-bits in `bitfield`, modulo 2.
 *
 * For instance, `bitfield_parity32(field)` of the below 32-bit value returns
 * `1`.
 *
 *     field:  0b00000000'00000000'11111111'00010000
 *     index:   31                                 0
 *
 * This is the canonical definition for the GCC/Clang builtin
 * `__builtin_parity`, and hence returns a signed integer.
 *
 * @param bitfield Bitfield to count 1-bits from.
 * @return The number of 1-bits in `bitfield`, modulo 2.
 */
BITFIELD_WARN_UNUSED_RESULT
inline int32_t bitfield_parity32(uint32_t bitfield) {
  return __builtin_parity(bitfield);
}

/**
 * Byte Swap
 *
 * Returns `field` with the order of the bytes reversed. Bytes here always means
 * exactly 8 bits.
 *
 * For instance, `byteswap(field)` of the below 32-bit value returns `1`.
 *
 *     field:  0bAAAAAAAA'BBBBBBBB'CCCCCCCC'DDDDDDDD
 *     index:   31                                 0
 *    returns: 0bDDDDDDDD'CCCCCCCC'BBBBBBBB'AAAAAAAA
 *
 * This is the canonical definition for the GCC/Clang builtin
 * `__builtin_bswap32`.
 *
 * @param bitfield Bitfield to reverse bytes of.
 * @return `bitfield` with the order of bytes reversed.
 */
BITFIELD_WARN_UNUSED_RESULT
inline uint32_t bitfield_byteswap32(uint32_t bitfield) {
  return __builtin_bswap32(bitfield);
}

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_BITFIELD_H_
