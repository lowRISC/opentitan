// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/base/boot_measurements.h"

// Boot measurements.
//
// This is placed at a fixed location in memory within the .static_critical
// section. It will be populated by the ROM before the jump to ROM_EXT.
OT_SET_BSS_SECTION(".static_critical.boot_measurements",
                   boot_measurements_t boot_measurements;)
