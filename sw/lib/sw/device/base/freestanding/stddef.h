// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_FREESTANDING_STDDEF_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_FREESTANDING_STDDEF_H_

#include <stdalign.h>
#include <stdint.h>

/**
 * @file
 * @brief C library Common definitions (Freestanding)
 *
 * This header implements the stdint.h standard header, as required by C11 S4p6.
 * This header is specified in detail in S7.19 of the same.
 *
 * See https://github.com/riscv/riscv-elf-psabi-doc/blob/master/riscv-elf.md
 * for the RISC-V specifics this file conforms to.
 */

/**
 * @internal
 * GCC's built-in defines do not include a type with the maximum alignment, but
 * does include a define with the maximum alignment value. Since the only
 * requirement of `max_align_t` is that it be some type such that its alignment
 * is maximal, we simply use a one-byte struct whose alignment is forced to be
 * the maximum.
 */
typedef struct {
  alignas(__BIGGEST_ALIGNMENT__) uint8_t __nonce; /**< @private **/
} max_align_t;

typedef __PTRDIFF_TYPE__ ptrdiff_t;
typedef __SIZE_TYPE__ size_t;
typedef __WCHAR_TYPE__ wchar_t;

#define NULL ((void *)0) /**< @hideinitializer */
#define offsetof(type, member) \
  __builtin_offsetof(type, member) /**< @hideinitializer */

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_FREESTANDING_STDDEF_H_
