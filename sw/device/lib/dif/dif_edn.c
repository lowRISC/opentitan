// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_edn.h"

#include "edn_regs.h"  // Generated

OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_stop(const dif_edn_t *edn) {
  if (edn == NULL) {
    return kDifBadArg;
  }

  mmio_region_write32(edn->base_addr, EDN_CTRL_REG_OFFSET, EDN_CTRL_REG_RESVAL);

  return kDifOk;
}
