// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom/rom_cfi.h"

#include "sw/device/silicon_creator/lib/cfi.h"

// Define counters table variable required by the CFI counter macros.
CFI_DEFINE_COUNTERS(rom_counters, ROM_CFI_FUNC_COUNTERS_TABLE);
