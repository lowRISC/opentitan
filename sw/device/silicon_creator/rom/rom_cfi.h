// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_ROM_CFI_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_ROM_CFI_H_

#include "sw/device/silicon_creator/lib/cfi.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Table of forward branch Control Flow Integrity (CFI) counters.
 *
 * Columns: Name, Initital Value.
 *
 * Each counter is indexed by Name. The Initial Value is used to initialize the
 * counters with unique values with a good hamming distance. The values are
 * restricted to 11-bit to be able use immediate load instructions.

 * Encoding generated with
 * $ ./util/design/sparse-fsm-encode.py -d 6 -m 6 -n 11 \
 *     -s 1630646358 --language=c
 *
 * Minimum Hamming distance: 6
 * Maximum Hamming distance: 8
 * Minimum Hamming weight: 5
 * Maximum Hamming weight: 8
 */
// clang-format off
#define ROM_CFI_FUNC_COUNTERS_TABLE(X) \
  X(kCfiRomMain,         0x14b) \
  X(kCfiRomInit,         0x7dc) \
  X(kCfiRomVerify,       0x5a7) \
  X(kCfiRomTryBoot,      0x235) \
  X(kCfiRomPreBootCheck, 0x43a) \
  X(kCfiRomBoot,         0x2e2)
// clang-format on

// Define counters constant values required by the CFI counter macros.
CFI_DEFINE_COUNTER_CONSTANTS(ROM_CFI_FUNC_COUNTERS_TABLE);

// Declare counters table variable required by the CFI counter macros.
CFI_DECLARE_COUNTERS(rom_counters);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_ROM_CFI_H_
