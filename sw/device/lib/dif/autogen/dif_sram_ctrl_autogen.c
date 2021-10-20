// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This file is auto-generated.

#include "sw/device/lib/dif/autogen/dif_sram_ctrl_autogen.h"

#include "sram_ctrl_regs.h"  // Generated.

OT_WARN_UNUSED_RESULT
dif_result_t dif_sram_ctrl_init(mmio_region_t base_addr,
                                dif_sram_ctrl_t *sram_ctrl) {
  if (sram_ctrl == NULL) {
    return kDifBadArg;
  }

  sram_ctrl->base_addr = base_addr;

  return kDifOk;
}
