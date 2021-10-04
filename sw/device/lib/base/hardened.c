// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/hardened.h"

// Instantiate inline functions in this TU.
extern uint32_t launder32(uint32_t);
extern uint32_t launderw(uintptr_t);
extern void barrier32(uint32_t);
extern void barrierw(uintptr_t);
