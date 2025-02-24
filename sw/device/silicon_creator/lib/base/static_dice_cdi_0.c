// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/base/static_dice_cdi_0.h"

#include "sw/device/lib/base/macros.h"

// CDI 0 cert signed by immutable ROM_EXT.
//
// This is placed at a fixed location in memory within the
// .static_dice section. It will be populated by the immutable
// ROM_EXT before the jump to mutable ROM_EXT.
OT_SET_BSS_SECTION(".static_dice.cdi_0",
                   OT_USED static_dice_cdi_0_t static_dice_cdi_0;)
