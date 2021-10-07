// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/runtime/ibex.h"

#include "sw/device/lib/base/csr.h"

extern uint64_t ibex_mcycle_read(void);

uint32_t ibex_mcause_read(void) {
  uint32_t mtval;
  CSR_READ(CSR_REG_MCAUSE, &mtval);
  return mtval;
}

uint32_t ibex_mtval_read(void) {
  uint32_t mtval;
  CSR_READ(CSR_REG_MTVAL, &mtval);
  return mtval;
}

extern ibex_timeout_t ibex_timeout_init(uint32_t timeout_usec);
extern bool ibex_timeout_check(const ibex_timeout_t *timeout);
