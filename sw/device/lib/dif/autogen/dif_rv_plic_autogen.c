// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This file is auto-generated.

#include "sw/device/lib/dif/autogen/dif_rv_plic_autogen.h"

#include "rv_plic_regs.h"  // Generated.

OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_plic_init(mmio_region_t base_addr, dif_rv_plic_t *rv_plic) {
  if (rv_plic == NULL) {
    return kDifBadArg;
  }

  rv_plic->base_addr = base_addr;

  return kDifOk;
}
