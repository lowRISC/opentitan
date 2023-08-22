// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/ip/flash_ctrl/driver/flash_ctrl.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "sw/lib/sw/device/silicon_creator/base/chip.h"

static_assert(CHIP_BL0_SIZE_MAX <= ((TOP_EARLGREY_EFLASH_SIZE_BYTES / 2) -
                                    CHIP_ROM_EXT_SIZE_MAX),
              "`CHIP_BL0_SIZE_MAX` is too large");
