// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/runtime/ibex.h"

#include "sw/device/lib/base/csr.h"

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

uint32_t ibex_mepc_read(void) {
  uint32_t mepc;
  CSR_READ(CSR_REG_MEPC, &mepc);
  return mepc;
}

void ibex_mepc_write(uint32_t mepc) { CSR_WRITE(CSR_REG_MEPC, mepc); }

// `extern` declarations to give the inline functions in the
// corresponding header a link location.

extern uint64_t ibex_mcycle_read(void);
extern ibex_timeout_t ibex_timeout_init(uint32_t timeout_usec);
extern bool ibex_timeout_check(const ibex_timeout_t *timeout);
extern uint64_t ibex_timeout_elapsed(const ibex_timeout_t *timeout);
