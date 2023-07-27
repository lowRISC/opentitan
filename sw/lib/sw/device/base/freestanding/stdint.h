// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_FREESTANDING_STDINT_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_FREESTANDING_STDINT_H_

/**
 * @file
 * @brief C library Integer types (Freestanding)
 *
 * This header implements the stdint.h standard header, as required by C11 S4p6.
 * This header is specified in detail in S7.20 the same.
 *
 * Actual limit values below are defined as:
 * - Unsigned MAXs are defined as the `0xff..ffU` all-ones representation.
 * - Signed MINs are defined as `0x80..00` all-zeroes-but-the-last
 *   representation.
 * - Unsigned MAXs are defined as `0x7f..ff` all-ones-but-the-last
 *   representation.
 * These shorthands are correct for two's complement and the ones least likely
 * to get a mistake in.
 *
 * It goes without saying that this file assumes the underlying representation
 * is two's complement and little-endian.
 *
 * See https://github.com/riscv/riscv-elf-psabi-doc/blob/master/riscv-elf.md
 * for the RISC-V specifics this file conforms to.
 */

typedef __UINT8_TYPE__ uint8_t;
typedef __UINT16_TYPE__ uint16_t;
typedef __UINT32_TYPE__ uint32_t;
typedef __UINT64_TYPE__ uint64_t;
typedef __INT8_TYPE__ int8_t;
typedef __INT16_TYPE__ int16_t;
typedef __INT32_TYPE__ int32_t;
typedef __INT64_TYPE__ int64_t;

typedef __UINT_LEAST8_TYPE__ uint_least8_t;
typedef __UINT_LEAST16_TYPE__ uint_least16_t;
typedef __UINT_LEAST32_TYPE__ uint_least32_t;
typedef __UINT_LEAST64_TYPE__ uint_least64_t;
typedef __INT_LEAST8_TYPE__ int_least8_t;
typedef __INT_LEAST16_TYPE__ int_least16_t;
typedef __INT_LEAST32_TYPE__ int_least32_t;
typedef __INT_LEAST64_TYPE__ int_least64_t;

typedef __UINT_FAST8_TYPE__ uint_fast8_t;
typedef __UINT_FAST16_TYPE__ uint_fast16_t;
typedef __UINT_FAST32_TYPE__ uint_fast32_t;
typedef __UINT_FAST64_TYPE__ uint_fast64_t;
typedef __INT_FAST8_TYPE__ int_fast8_t;
typedef __INT_FAST16_TYPE__ int_fast16_t;
typedef __INT_FAST32_TYPE__ int_fast32_t;
typedef __INT_FAST64_TYPE__ int_fast64_t;

typedef __UINTPTR_TYPE__ uintptr_t;
typedef __INTPTR_TYPE__ intptr_t;

typedef __UINTMAX_TYPE__ uintmax_t;
typedef __INTMAX_TYPE__ intmax_t;

// NOTE: Below, we use GCC/Clang's built-in defines for limits. However, only
// MAX limits are provided and, as such, we define a signed MIN, given a MAX, as
// (-MIN - 1). (MAX + 1) will trigger signed overflow and, as such, Undefined
// Behavior.

#define INT8_MIN (-__INT8_MAX__ - 1)   /**< @hideinitializer */
#define INT8_MAX __INT8_MAX__          /**< @hideinitializer */
#define UINT8_MAX __UINT8_MAX__        /**< @hideinitializer */
#define INT16_MIN (-__INT16_MAX__ - 1) /**< @hideinitializer */
#define INT16_MAX __INT16_MAX__        /**< @hideinitializer */
#define UINT16_MAX __UINT16_MAX__      /**< @hideinitializer */
#define INT32_MIN (-__INT32_MAX__ - 1) /**< @hideinitializer */
#define INT32_MAX __INT32_MAX__        /**< @hideinitializer */
#define UINT32_MAX __UINT32_MAX__      /**< @hideinitializer */
#define INT64_MIN (-__INT64_MAX__ - 1) /**< @hideinitializer */
#define INT64_MAX __INT64_MAX__        /**< @hideinitializer */
#define UINT64_MAX __UINT64_MAX__      /**< @hideinitializer */

#define INT_LEAST8_MIN (-__INT_LEAST8_MAX__ - 1)   /**< @hideinitializer */
#define INT_LEAST8_MAX __INT_LEAST8_MAX__          /**< @hideinitializer */
#define UINT_LEAST8_MAX __UINT_LEAST8_MAX__        /**< @hideinitializer */
#define INT_LEAST16_MIN (-__INT_LEAST16_MAX__ - 1) /**< @hideinitializer */
#define INT_LEAST16_MAX __INT_LEAST16_MAX__        /**< @hideinitializer */
#define UINT_LEAST16_MAX __UINT_LEAST16_MAX__      /**< @hideinitializer */
#define INT_LEAST32_MIN (-__INT_LEAST32_MAX__ - 1) /**< @hideinitializer */
#define INT_LEAST32_MAX __INT_LEAST32_MAX__        /**< @hideinitializer */
#define UINT_LEAST32_MAX __UINT_LEAST32_MAX__      /**< @hideinitializer */
#define INT_LEAST64_MIN (-__INT_LEAST64_MAX__ - 1) /**< @hideinitializer */
#define INT_LEAST64_MAX __INT_LEAST64_MAX__        /**< @hideinitializer */
#define UINT_LEAST64_MAX __UINT_LEAST64_MAX__      /**< @hideinitializer */

#define INT_FAST8_MIN (-__INT_FAST8_MAX__ - 1)   /**< @hideinitializer */
#define INT_FAST8_MAX __INT_FAST8_MAX__          /**< @hideinitializer */
#define UINT_FAST8_MAX __UINT_FAST8_MAX__        /**< @hideinitializer */
#define INT_FAST16_MIN (-__INT_FAST16_MAX__ - 1) /**< @hideinitializer */
#define INT_FAST16_MAX __INT_FAST16_MAX__        /**< @hideinitializer */
#define UINT_FAST16_MAX __UINT_FAST16_MAX__      /**< @hideinitializer */
#define INT_FAST32_MIN (-__INT_FAST32_MAX__ - 1) /**< @hideinitializer */
#define INT_FAST32_MAX __INT_FAST32_MAX__        /**< @hideinitializer */
#define UINT_FAST32_MAX __UINT_FAST32_MAX__      /**< @hideinitializer */
#define INT_FAST64_MIN (-__INT_FAST64_MAX__ - 1) /**< @hideinitializer */
#define INT_FAST64_MAX __INT_FAST64_MAX__        /**< @hideinitializer */
#define UINT_FAST64_MAX __UINT_FAST64_MAX__      /**< @hideinitializer */

#define INTPTR_MIN (-__INTPTR_MAX__ - 1) /**< @hideinitializer */
#define INTPTR_MAX __INTPTR_MAX__        /**< @hideinitializer */
#define UINTPTR_MAX __UINTPTR_MAX__      /**< @hideinitializer */

#define INTMAX_MIN (-__INTMAX_MAX__ - 1) /**< @hideinitializer */
#define INTMAX_MAX __INTMAX_MAX__        /**< @hideinitializer */
#define UINTMAX_MAX __UINTMAX_MAX__      /**< @hideinitializer */

#define PTRDIFF_MIN (-__PTRDIFF_MAX__ - 1) /**< @hideinitializer */
#define PTRDIFF_MAX __PTRDIFF_MAX__        /**< @hideinitializer */

#define SIZE_MAX __SIZE_MAX__ /**< @hideinitializer */

#define WCHAR_MIN (-__WCHAR_MAX__ - 1) /**< @hideinitializer */
#define WCHAR_MAX __WCHAR_MAX__        /**< @hideinitializer */

// NOTE: While GCC and Clang both provide macros for implememting the _C macros,
// they are inconsistent on which is correct, so we implement them ourselves
// below.

#define INT8_C(value) (value)       /**< @hideinitializer */
#define INT16_C(value) (value)      /**< @hideinitializer */
#define INT32_C(value) (value)      /**< @hideinitializer */
#define INT64_C(value) (value##LL)  /**< @hideinitializer */
#define INTMAX_C(value) (value##LL) /**< @hideinitializer */

#define UINT8_C(value) (value##U)     /**< @hideinitializer */
#define UINT16_C(value) (value##U)    /**< @hideinitializer */
#define UINT32_C(value) (value##U)    /**< @hideinitializer */
#define UINT64_C(value) (value##ULL)  /**< @hideinitializer */
#define UINTMAX_C(value) (value##ULL) /**< @hideinitializer */

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_FREESTANDING_STDINT_H_
