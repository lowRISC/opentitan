// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom_ext/rom_ext_epmp.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/csr.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

void rom_ext_epmp_unlock_owner_stage_rx(epmp_state_t *state,
                                        epmp_region_t region) {
  const int kEntry = 8;
  epmp_state_configure_tor(state, kEntry, region, kEpmpPermLockedReadExecute);

  // Update the hardware configuration (CSRs).
  //
  // Entry is hardcoded as 8. Make sure to modify hardcoded values if changing
  // kEntry.
  //
  // The `pmp1cfg` configuration is the second field in `pmpcfg0`.
  //
  //            32          24          16           8           0
  //             +-----------+-----------+-----------+-----------+
  // `pmpcfg2` = | `pmp11cfg | `pmp10cfg`| `pmp9cfg` | `pmp8cfg` |
  //             +-----------+-----------+-----------+-----------+
  CSR_WRITE(CSR_REG_PMPADDR7, ((uint32_t)region.start) >> 2);
  CSR_WRITE(CSR_REG_PMPADDR8, ((uint32_t)region.end) >> 2);
  CSR_CLEAR_BITS(CSR_REG_PMPCFG2, 0xff);
  CSR_SET_BITS(CSR_REG_PMPCFG2, (kEpmpModeTor | kEpmpPermLockedReadExecute));
}

void rom_ext_epmp_unlock_owner_stage_r(epmp_state_t *state,
                                       epmp_region_t region) {
  const int kEntry = 9;
  epmp_state_configure_napot(state, kEntry, region, kEpmpPermLockedReadOnly);

  // Update the hardware configuration (CSRs).
  //
  // Entry is hardcoded as 9. Make sure to modify hardcoded values if changing
  // kEntry.
  //
  // The `pmp6cfg` configuration is the second field in `pmpcfg1`.
  //
  //            32          24          16           8           0
  //             +-----------+-----------+-----------+-----------+
  // `pmpcfg2` = | `pmp11cfg`| `pmp10cfg`| `pmp9cfg` | `pmp8cfg` |
  //             +-----------+-----------+-----------+-----------+
  CSR_WRITE(CSR_REG_PMPADDR9,
            (uint32_t)region.start >> 2 |
                ((uint32_t)region.end - (uint32_t)region.start - 1) >> 3);
  CSR_CLEAR_BITS(CSR_REG_PMPCFG2, 0xff << 8);
  CSR_SET_BITS(CSR_REG_PMPCFG2,
               ((kEpmpModeNapot | kEpmpPermLockedReadOnly) << 8));
}
