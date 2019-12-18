// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/runtime/ibex.h"

#ifdef SIMULATION
const size_t kIbexClockFreqHz = 500 * 1000;  // 500 kHz
#else
const size_t kIbexClockFreqHz = 50 * 1000 * 1000;  // 50 MHz
#endif

extern void ibex_busy_loop(size_t);
