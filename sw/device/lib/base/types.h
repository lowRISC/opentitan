// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef SW_DEVICE_LIB_BASE_TYPES_H_
#define SW_DEVICE_LIB_BASE_TYPES_H_

/**
 * Standard C type definitions; compare the standard header <stddef.h>.
 *
 * Numeric definitions here are *specifically* tailored to the R32I calling 
 * convention, as described in
 * https://riscv.org/wp-content/uploads/2015/01/riscv-calling.pdf.
 */

typedef unsigned char uint8;
typedef unsigned short uint16;
typedef unsigned int uint32;
typedef unsigned long long uint64;

typedef uint64 uintmax;
typedef uint32 uintptr;

typedef signed char int8;
typedef signed short int16;
typedef signed int int32;
typedef signed long long int64;

typedef int64 intmax;
typedef int32 intptr;

typedef uintptr usize;
typedef intptr ptrdiff;

#define NULL 0

// Cribbed from https://clang.llvm.org/doxygen/stdbool_8h_source.html.

#define bool _Bool
#define true 1
#define false 0

#endif  // SW_DEVICE_LIB_BASE_TYPES_H_