// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef SW_DEVICE_LIB_BASE_MACROS_H_
#define SW_DEVICE_LIB_BASE_MACROS_H_

/**
 * Miscellaneous macros, which provide encapsulation for compiler-specific
 * constructs.
 */

#define NO_RETURN __attribute__((noreturn))
#define LINK_SECTION(name) __attribute__((section("" name "")))
#define ALIGN_AS(bytes) __attribute__((aligned(bytes)))
#define IRQ_FN __attribute__((aligned(4), interrupt, weak))
#define NAKED_FN __attribute__((naked))

#endif  // SW_DEVICE_LIB_BASE_MACROS_H_