// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_edn.h"

#include "edn_regs.h"  // Generated

dif_result_t dif_edn_init(mmio_region_t base_addr, dif_edn_t *edn) {
  if (edn == NULL) {
    return kDifBadArg;
  }

  edn->base_addr = base_addr;

  return kDifOk;
}
