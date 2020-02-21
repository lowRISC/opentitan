// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_FREESTANDING_LIMITS_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_FREESTANDING_LIMITS_H_

#include <stdint.h>

/**
 * @file
 * @brief C library Sizes of integer types (Freestanding)
 *
 * This header implements the limits.h standard header, as required by C11 S4p6.
 * This header is specified in detail in S7.10 and S5.2.4.2.1 of the same.
 */

#define SCHAR_MAX __SCHAR_MAX__     /**< @hideinitializer */
#define SHRT_MAX __SHRT_MAX__       /**< @hideinitializer */
#define INT_MAX __INT_MAX__         /**< @hideinitializer */
#define LONG_MAX __LONG_MAX__       /**< @hideinitializer */
#define LLONG_MAX __LONG_LONG_MAX__ /**< @hideinitializer */

#define SCHAR_MIN (-__SCHAR_MAX__ - 1)       /**< @hideinitializer */
#define SHRT_MIN (-__SHRT_MAX__ - 1)         /**< @hideinitializer */
#define INT_MIN (-__INT_MAX__ - 1)           /**< @hideinitializer */
#define LONG_MIN (-__LONG_MAX__ - 1L)        /**< @hideinitializer */
#define LLONG_MIN (-__LONG_LONG_MAX__ - 1LL) /**< @hideinitializer */

#define UCHAR_MAX (__SCHAR_MAX__ * 2 + 1)            /**< @hideinitializer */
#define USHRT_MAX (__SHRT_MAX__ * 2 + 1)             /**< @hideinitializer */
#define UINT_MAX (__INT_MAX__ * 2U + 1U)             /**< @hideinitializer */
#define ULONG_MAX (__LONG_MAX__ * 2UL + 1UL)         /**< @hideinitializer */
#define ULLONG_MAX (__LONG_LONG_MAX__ * 2ULL + 1ULL) /**< @hideinitializer */

#define CHAR_BIT __CHAR_BIT__ /**< @hideinitializer */
#define MB_LEN_MAX (1)        /**< @hideinitializer */

#ifdef __CHAR_UNSIGNED__
#define CHAR_MIN (0)       /**< @hideinitializer */
#define CHAR_MAX UCHAR_MAX /**< @hideinitializer */
#else
#define CHAR_MIN SCHAR_MIN /**< @hideinitializer */
#define CHAR_MAX SCHAR_MAX /**< @hideinitializer */
#endif

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_FREESTANDING_LIMITS_H_
