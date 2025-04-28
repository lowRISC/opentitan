// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/ibex.h"

#include "dt/dt_rv_core_ibex.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"

#include "rv_core_ibex_regs.h"

static_assert(kDtRvCoreIbexCount == 1,
              "this code requires exactly one rv_core_ibex");
const dt_rv_core_ibex_t kRvCoreIbexDt = kDtRvCoreIbexFirst;

static inline uint32_t rv_core_ibex_base(void) {
  return dt_rv_core_ibex_primary_reg_block(kRvCoreIbexDt);
}

status_t ibex_wait_rnd_valid(void) {
  while (true) {
    uint32_t reg = abs_mmio_read32(rv_core_ibex_base() +
                                   RV_CORE_IBEX_RND_STATUS_REG_OFFSET);
    if (bitfield_bit32_read(reg, RV_CORE_IBEX_RND_STATUS_RND_DATA_VALID_BIT)) {
      return OK_STATUS();
    }
  }
}

status_t ibex_rnd_status_read(uint32_t *rnd_status) {
  *rnd_status =
      abs_mmio_read32(rv_core_ibex_base() + RV_CORE_IBEX_RND_STATUS_REG_OFFSET);
  return OK_STATUS();
}

status_t ibex_rnd_data_read(uint32_t *rnd_data) {
  *rnd_data =
      abs_mmio_read32(rv_core_ibex_base() + RV_CORE_IBEX_RND_DATA_REG_OFFSET);
  return OK_STATUS();
}
