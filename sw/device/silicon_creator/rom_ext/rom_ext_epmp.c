// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom_ext/rom_ext_epmp.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/csr.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

void rom_ext_epmp_unlock_owner_stage_rx(epmp_state_t *state,
                                        epmp_region_t image) {
  const int kEntry = 1;
  epmp_state_configure_tor(state, kEntry, image, kEpmpPermLockedReadExecute);

  // Update the hardware configuration (CSRs).
  //
  // Entry is hardcoded as 1. Make sure to modify hardcoded values if changing
  // kEntry.
  //
  // The `pmp1cfg` configuration is the second field in `pmpcfg0`.
  //
  //            32          24          16           8           0
  //             +-----------+-----------+-----------+-----------+
  // `pmpcfg0` = | `pmp3cfg` | `pmp2cfg` | `pmp1cfg` | `pmp0cfg` |
  //             +-----------+-----------+-----------+-----------+
  CSR_WRITE(CSR_REG_PMPADDR0, ((uint32_t)image.start) >> 2);
  CSR_WRITE(CSR_REG_PMPADDR1, ((uint32_t)image.end) >> 2);
  CSR_CLEAR_BITS(CSR_REG_PMPCFG0, 0xff00);
  CSR_SET_BITS(CSR_REG_PMPCFG0, (kEpmpModeTor | kEpmpPermLockedReadExecute)
                                    << 8);
}
