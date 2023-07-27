// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_FREESTANDING_ASSERT_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_FREESTANDING_ASSERT_H_

/**
 * @file
 * @brief C library diagnostics
 *
 * This header implements the assert.h standard header, specified in S7.2 of
 * C11.
 *
 * While not required by S4p6 as part of freestanding C, this file is useful
 * because it gives us a consistent spelling of `static_assert` across C and
 * C++. `assert` should not be used in device code.
 */

// Note that `static_assert` is a C++ keyword, so we only need this to be
// defined for C.
#ifndef __cplusplus
#define static_assert _Static_assert
#endif  // __cplusplus

// `assert()` should not be used. When building with Clang, using this function
// in device code will emit a compile-time error.
#define assert(do_not_use) \
  static_assert(false, "do not use assert(); use CHECK() instead")

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_FREESTANDING_ASSERT_H_
