// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This file is auto-generated.

#include "sw/device/lib/dif/autogen/dif_lc_ctrl_autogen.h"
#include <stdint.h>

#include "lc_ctrl_regs.h"  // Generated.

OT_WARN_UNUSED_RESULT
dif_result_t dif_lc_ctrl_init(mmio_region_t base_addr, dif_lc_ctrl_t *lc_ctrl) {
  if (lc_ctrl == NULL) {
    return kDifBadArg;
  }

  lc_ctrl->base_addr = base_addr;

  return kDifOk;
}
