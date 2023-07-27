// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_FREESTANDING_STDARG_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_FREESTANDING_STDARG_H_

/**
 * @file
 * @brief C library Variable arguments (Freestanding)
 *
 * This header implements the stdarg.h standard header, as required by C11 S4p6.
 * This header is specified in detail in S7.16.
 *
 * The compiler intrinsics below are cribbed from
 * https://clang.llvm.org/doxygen/stdarg_8h_source.html
 */

typedef __builtin_va_list va_list;
#define va_start(ap, param) \
  __builtin_va_start(ap, param)                       /**< @hideinitializer */
#define va_end(ap) __builtin_va_end(ap)               /**< @hideinitializer */
#define va_arg(ap, type) __builtin_va_arg(ap, type)   /**< @hideinitializer */
#define va_copy(dst, src) __builtin_va_copy(dst, src) /**< @hideinitializer */

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_FREESTANDING_STDARG_H_
