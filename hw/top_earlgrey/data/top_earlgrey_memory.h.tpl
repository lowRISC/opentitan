// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _TOP_${top["name"].upper()}_MEMORY_H_
#define _TOP_${top["name"].upper()}_MEMORY_H_

/**
 * @file
 * @brief Assembler-only Top-Specific Definitions.
 *
 * This file contains preprocessor definitions for use within assembly code.
 *
 * These are not shared with C/C++ code because these are only allowed to be
 * preprocessor definitions, no data or type declarations are allowed. The
 * assembler is also stricter about literals (not allowing suffixes for
 * signed/unsigned which are sensible to use for unsigned values in C/C++).
 */

// Include guard for assembler
#ifdef __ASSEMBLER__

% for m in top["memory"]:
/**
 * Memory base address for ${m["name"]} in top ${top["name"]}.
 */
#define TOP_${top["name"].upper()}_${m["name"].upper()}_BASE_ADDR ${m["base_addr"]}

/**
 * Memory size for ${m["name"]} in top ${top["name"]}.
 */
#define TOP_${top["name"].upper()}_${m["name"].upper()}_SIZE_BYTES ${m["size"]}

% endfor

#endif  // __ASSEMBLER__

#endif  // _TOP_${top["name"].upper()}_MEMORY_H_
