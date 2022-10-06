// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/base/boot_measurements.h"

#include "sw/device/lib/base/macros.h"

// This symbol is declared as weak so that the ROM and ROM_EXT may
// override its location.
OT_WEAK boot_measurements_t boot_measurements;
