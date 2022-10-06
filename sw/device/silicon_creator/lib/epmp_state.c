// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/epmp_state.h"

#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/hardened.h"

// The context is declared as weak so that the ROM and ROM_EXT may
// override its location.
OT_WEAK epmp_state_t epmp_state;

/**
 * Extern declarations of inline functions.
 */
extern void epmp_state_configure_tor(uint32_t entry, epmp_region_t region,
                                     epmp_perm_t perm);
extern void epmp_state_configure_na4(uint32_t entry, epmp_region_t region,
                                     epmp_perm_t perm);
extern void epmp_state_configure_napot(uint32_t entry, epmp_region_t region,
                                       epmp_perm_t perm);

rom_error_t epmp_state_check(void) {
  uint32_t checks = 0;
  const epmp_state_t *s = &epmp_state;
#define CHECK_CSR(reg, value) \
  do {                        \
    uint32_t csr;             \
    CSR_READ(reg, &csr);      \
    checks += csr == (value); \
  } while (false)

  // Check address registers.
  CHECK_CSR(CSR_REG_PMPADDR0, s->pmpaddr[0]);
  CHECK_CSR(CSR_REG_PMPADDR1, s->pmpaddr[1]);
  CHECK_CSR(CSR_REG_PMPADDR2, s->pmpaddr[2]);
  CHECK_CSR(CSR_REG_PMPADDR3, s->pmpaddr[3]);
  CHECK_CSR(CSR_REG_PMPADDR4, s->pmpaddr[4]);
  CHECK_CSR(CSR_REG_PMPADDR5, s->pmpaddr[5]);
  CHECK_CSR(CSR_REG_PMPADDR6, s->pmpaddr[6]);
  CHECK_CSR(CSR_REG_PMPADDR7, s->pmpaddr[7]);
  CHECK_CSR(CSR_REG_PMPADDR8, s->pmpaddr[8]);
  CHECK_CSR(CSR_REG_PMPADDR9, s->pmpaddr[9]);
  CHECK_CSR(CSR_REG_PMPADDR10, s->pmpaddr[10]);
  CHECK_CSR(CSR_REG_PMPADDR11, s->pmpaddr[11]);
  CHECK_CSR(CSR_REG_PMPADDR12, s->pmpaddr[12]);
  CHECK_CSR(CSR_REG_PMPADDR13, s->pmpaddr[13]);
  CHECK_CSR(CSR_REG_PMPADDR14, s->pmpaddr[14]);
  CHECK_CSR(CSR_REG_PMPADDR15, s->pmpaddr[15]);

  // Check configuration registers.
  CHECK_CSR(CSR_REG_PMPCFG0, s->pmpcfg[0]);
  CHECK_CSR(CSR_REG_PMPCFG1, s->pmpcfg[1]);
  CHECK_CSR(CSR_REG_PMPCFG2, s->pmpcfg[2]);
  CHECK_CSR(CSR_REG_PMPCFG3, s->pmpcfg[3]);

  // Check Machine Security Configuration (MSECCFG) register.
  // High bits are hardcoded to 0.
  CHECK_CSR(CSR_REG_MSECCFG, s->mseccfg);
  CHECK_CSR(CSR_REG_MSECCFGH, 0);

#undef CHECK_CSR

  enum { kTotalChecks = 22 };
  // Hamming distance of 3, error = 0x72f, kErrorOk = 0x739.
  rom_error_t error = kErrorOk ^ kTotalChecks;
  if (launder32(checks) == kTotalChecks) {
    HARDENED_CHECK_EQ(checks, kTotalChecks);
    error ^= checks;
    HARDENED_CHECK_EQ(error, kErrorOk);
    return error;
  }
  return kErrorEpmpBadCheck;
}
