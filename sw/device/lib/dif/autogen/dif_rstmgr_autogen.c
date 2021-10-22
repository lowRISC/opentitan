// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This file is auto-generated.

#include "sw/device/lib/dif/autogen/dif_rstmgr_autogen.h"
#include <stdint.h>

#include "rstmgr_regs.h"  // Generated.

OT_WARN_UNUSED_RESULT
dif_result_t dif_rstmgr_init(mmio_region_t base_addr, dif_rstmgr_t *rstmgr) {
  if (rstmgr == NULL) {
    return kDifBadArg;
  }

  rstmgr->base_addr = base_addr;

  return kDifOk;
}
