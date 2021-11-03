// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/device/lib/dif/autogen/dif_clkmgr_autogen.h"
#include <stdint.h>

#include "clkmgr_regs.h"  // Generated.

OT_WARN_UNUSED_RESULT
dif_result_t dif_clkmgr_init(mmio_region_t base_addr, dif_clkmgr_t *clkmgr) {
  if (clkmgr == NULL) {
    return kDifBadArg;
  }

  clkmgr->base_addr = base_addr;

  return kDifOk;
}
