// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/epmp.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/epmp_state.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define EPMP_SET(cfg_reg, addr_reg, mask, cfg, addr) \
  CSR_CLEAR_BITS(CSR_REG_PMPCFG##cfg_reg, mask);     \
  CSR_WRITE(CSR_REG_PMPADDR##addr_reg, pmpaddr);     \
  CSR_SET_BITS(CSR_REG_PMPCFG##cfg_reg, cfg);

static void epmp_set(uint8_t entry, uint32_t pmpcfg, uint32_t pmpaddr) {
  uint32_t shift = 8 * (entry % 4);
  uint32_t mask = 0xFFu << shift;
  uint32_t cfg = (pmpcfg & 0xFFu) << shift;
  HARDENED_CHECK_LT(entry, 16);
  switch (entry) {
    // clang-format off
    case  0: EPMP_SET(0,  0, mask, cfg, pmpaddr); break;
    case  1: EPMP_SET(0,  1, mask, cfg, pmpaddr); break;
    case  2: EPMP_SET(0,  2, mask, cfg, pmpaddr); break;
    case  3: EPMP_SET(0,  3, mask, cfg, pmpaddr); break;
    case  4: EPMP_SET(1,  4, mask, cfg, pmpaddr); break;
    case  5: EPMP_SET(1,  5, mask, cfg, pmpaddr); break;
    case  6: EPMP_SET(1,  6, mask, cfg, pmpaddr); break;
    case  7: EPMP_SET(1,  7, mask, cfg, pmpaddr); break;
    case  8: EPMP_SET(2,  8, mask, cfg, pmpaddr); break;
    case  9: EPMP_SET(2,  9, mask, cfg, pmpaddr); break;
    case 10: EPMP_SET(2, 10, mask, cfg, pmpaddr); break;
    case 11: EPMP_SET(2, 11, mask, cfg, pmpaddr); break;
    case 12: EPMP_SET(3, 12, mask, cfg, pmpaddr); break;
    case 13: EPMP_SET(3, 13, mask, cfg, pmpaddr); break;
    case 14: EPMP_SET(3, 14, mask, cfg, pmpaddr); break;
    case 15: EPMP_SET(3, 15, mask, cfg, pmpaddr); break;
    // clang-format on
    default:
      // should be impossible to get here because of HARDENED_CHECK_LT above.
      HARDENED_TRAP();
  }
  uint32_t cfgent = entry / 4;
  epmp_state.pmpcfg[cfgent] = (epmp_state.pmpcfg[cfgent] & ~mask) | cfg;
  epmp_state.pmpaddr[entry] = pmpaddr;
}

void epmp_clear(uint8_t entry) { epmp_set(entry, kEpmpModeOff, 0); }

void epmp_set_napot(uint8_t entry, epmp_region_t region, epmp_perm_t perm) {
  uint32_t length = region.end - region.start;
  // The length must be 4 or more.
  HARDENED_CHECK_GE(length, 4);
  // The length must be a power of 2.
  HARDENED_CHECK_EQ(bitfield_popcount32(length), 1);
  // The start address must be naturally aligned with length.
  HARDENED_CHECK_EQ(region.start & (length - 1), 0);
  epmp_mode_t mode = length == 4 ? kEpmpModeNa4 : kEpmpModeNapot;
  uint32_t addr = (region.start >> 2) | ((length - 1) >> 3);
  epmp_set(entry, (uint32_t)mode | (uint32_t)perm, addr);
}

void epmp_set_tor(uint8_t entry, epmp_region_t region, epmp_perm_t perm) {
  uint32_t start = region.start >> 2;
  uint32_t end = ((region.end + 3u) & ~3u) >> 2;
  epmp_set(entry, kEpmpModeOff, start);
  epmp_set(entry + 1, (uint32_t)kEpmpModeTor | (uint32_t)perm, end);
}

void epmp_clear_rlb(void) {
  const uint32_t kMask = EPMP_MSECCFG_RLB;
  epmp_state.mseccfg &= ~kMask;
  CSR_CLEAR_BITS(CSR_REG_MSECCFG, kMask);
}
