// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

/**
 * Configures Ibex for SCA and FI.
 *
 * This function disables the iCache and the dummy instructions using the
 * CPU Control and Status Register (cpuctrlsts).
 *
 */
void sca_configure_cpu(void) {
  uint32_t cpuctrl_csr;
  // Get current config.
  CSR_READ(CSR_REG_CPUCTRL, &cpuctrl_csr);
  // Disable the iCache.
  cpuctrl_csr = bitfield_field32_write(
      cpuctrl_csr, (bitfield_field32_t){.mask = 0x1, .index = 0}, 0);
  // Disable dummy instructions.
  cpuctrl_csr = bitfield_field32_write(
      cpuctrl_csr, (bitfield_field32_t){.mask = 0x1, .index = 2}, 0);
  // Write back config.
  CSR_WRITE(CSR_REG_CPUCTRL, cpuctrl_csr);
}
