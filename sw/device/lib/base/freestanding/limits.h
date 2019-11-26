// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_FREESTANDING_LIMITS_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_FREESTANDING_LIMITS_H_

#include <stdint.h>

/**
 * This header implements the limits.h standard header, as required by C11 S4p6.
 * This header is specified in detail in S7.10 and S5.2.4.2.1 of the same.
 */

#define SCHAR_MAX __SCHAR_MAX__
#define SHRT_MAX __SHRT_MAX__
#define INT_MAX __INT_MAX__
#define LONG_MAX __LONG_MAX__
#define LLONG_MAX __LONG_LONG_MAX__

#define SCHAR_MIN (-__SCHAR_MAX__ - 1)
#define SHRT_MIN (-__SHRT_MAX__ - 1)
#define INT_MIN (-__INT_MAX__ - 1)
#define LONG_MIN (-__LONG_MAX__ - 1L)
#define LLONG_MIN (-__LONG_LONG_MAX__ - 1LL)

#define UCHAR_MAX (__SCHAR_MAX__ * 2 + 1)
#define USHRT_MAX (__SHRT_MAX__ * 2 + 1)
#define UINT_MAX (__INT_MAX__ * 2U + 1U)
#define ULONG_MAX (__LONG_MAX__ * 2UL + 1UL)
#define ULLONG_MAX (__LONG_LONG_MAX__ * 2ULL + 1ULL)

#define CHAR_BIT __CHAR_BIT__
#define MB_LEN_MAX (1)

#ifdef __CHAR_UNSIGNED__
#define CHAR_MIN (0)
#define CHAR_MAX UCHAR_MAX
#else
#define CHAR_MIN SCHAR_MIN
#define CHAR_MAX SCHAR_MAX
#endif

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_FREESTANDING_LIMITS_H_
