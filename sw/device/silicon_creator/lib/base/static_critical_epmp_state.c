// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/epmp_state.h"

// In-memory copy of the ePMP register configuration.
//
// This is placed at a fixed location in memory within the .static_critical
// section. It will be populated by the ROM before the jump to ROM_EXT.
OT_SET_BSS_SECTION(".static_critical.epmp_state", epmp_state_t epmp_state;)
