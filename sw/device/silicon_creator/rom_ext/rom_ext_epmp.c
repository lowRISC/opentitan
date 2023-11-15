// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom_ext/rom_ext_epmp.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/csr.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

void rom_ext_epmp_unlock_owner_stage_rx(epmp_region_t region) {
  const int kEntry = 1;
  epmp_state_configure_tor(kEntry, region, kEpmpPermLockedReadExecute);

  // Update the hardware configuration (CSRs).
  //
  // Entry is hardcoded as 1. Make sure to modify hardcoded values if changing
  // kEntry.
  //
  // The `pmp1cfg` configuration is the second field in `pmpcfg0`.
  //
  //            32          24          16           8           0
  //             +-----------+-----------+-----------+-----------+
  // `pmpcfg0` = |  `pmp3cfg |  `pmp2cfg`| `pmp1cfg` | `pmp0cfg` |
  //             +-----------+-----------+-----------+-----------+

  CSR_WRITE(CSR_REG_PMPADDR0, ((uint32_t)region.start) >> 2);
  CSR_WRITE(CSR_REG_PMPADDR1, ((uint32_t)region.end) >> 2);
  CSR_CLEAR_BITS(CSR_REG_PMPCFG0, 0xff << 8);
  CSR_SET_BITS(CSR_REG_PMPCFG0, (kEpmpModeTor | kEpmpPermLockedReadExecute)
                                    << 8);
}

void rom_ext_epmp_unlock_owner_stage_r(epmp_region_t region) {
  const int kEntry = 2;
  epmp_state_configure_napot(kEntry, region, kEpmpPermLockedReadOnly);

  // Update the hardware configuration (CSRs).
  //
  // Entry is hardcoded as 2. Make sure to modify hardcoded values if changing
  // kEntry.
  //
  // The `pmp2cfg` configuration is the third field in `pmpcfg0`.
  //
  //            32          24          16           8           0
  //             +-----------+-----------+-----------+-----------+
  // `pmpcfg0` = |  `pmp3cfg |  `pmp2cfg`| `pmp1cfg` | `pmp0cfg` |
  //             +-----------+-----------+-----------+-----------+
  CSR_WRITE(CSR_REG_PMPADDR2,
            (uint32_t)region.start >> 2 |
                ((uint32_t)region.end - (uint32_t)region.start - 1) >> 3);
  CSR_CLEAR_BITS(CSR_REG_PMPCFG0, 0xff << 16);
  CSR_SET_BITS(CSR_REG_PMPCFG0,
               ((kEpmpModeNapot | kEpmpPermLockedReadOnly) << 16));
}

void rom_ext_epmp_mmio_adjust(void) {
  const int kEntry = 11;
  epmp_region_t region = {
      .start = 0x40000000,
      .end = 0x50000000,
  };
  epmp_state_configure_napot(kEntry, region, kEpmpPermLockedReadWrite);

  // Update the hardware configuration (CSRs).
  //
  // Entry is hardcoded as 2. Make sure to modify hardcoded values if changing
  // kEntry.
  //
  // The `pmp11cfg` configuration is the fourth field in `pmpcfg2`.
  //
  //            32          24          16           8           0
  //             +-----------+-----------+-----------+-----------+
  // `pmpcfg2` = |  `pmp11cfg |  `pmp10cfg`| `pmp9cfg` | `pmp8cfg` |
  //             +-----------+-----------+-----------+-----------+
  CSR_WRITE(CSR_REG_PMPADDR11,
            (uint32_t)region.start >> 2 |
                ((uint32_t)region.end - (uint32_t)region.start - 1) >> 3);
  CSR_CLEAR_BITS(CSR_REG_PMPCFG2, 0xff << 24);
  CSR_SET_BITS(CSR_REG_PMPCFG2,
               ((kEpmpModeNapot | kEpmpPermLockedReadWrite) << 24));
}

void rom_ext_epmp_otp_dai_lockout(void) {
  const int kEntry = 10;
  epmp_region_t region = {
      .start = TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR,
      .end = TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR + 0x1000,
  };
  epmp_state_configure_napot(kEntry, region, kEpmpPermLockedNoAccess);

  // Update the hardware configuration (CSRs).
  //
  // Entry is hardcoded as 10. Make sure to modify hardcoded values if changing
  // kEntry.
  //
  // The `pmp11cfg` configuration is the third field in `pmpcfg2`.
  //
  //            32          24          16           8           0
  //             +-----------+-----------+-----------+-----------+
  // `pmpcfg2` = | `pmp11cfg`| `pmp10cfg`| `pmp9cfg` | `pmp8cfg` |
  //             +-----------+-----------+-----------+-----------+
  CSR_WRITE(CSR_REG_PMPADDR10,
            (uint32_t)region.start >> 2 |
                ((uint32_t)region.end - (uint32_t)region.start - 1) >> 3);
  CSR_CLEAR_BITS(CSR_REG_PMPCFG2, 0xff << 16);
  CSR_SET_BITS(CSR_REG_PMPCFG2,
               ((kEpmpModeNapot | kEpmpPermLockedNoAccess) << 16));
}
