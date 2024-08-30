// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/device/lib/dif/autogen/dif_rv_plic_autogen.h"

#include <stdint.h>

#include "sw/device/lib/dif/dif_base.h"

#include "rv_plic_regs.h"  // Generated.

OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_plic_init(mmio_region_t base_addr, dif_rv_plic_t *rv_plic) {
  if (rv_plic == NULL) {
    return kDifBadArg;
  }

  rv_plic->base_addr = base_addr;

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_plic_init_from_dt(const dt_rv_plic_t *dt,
                                      dif_rv_plic_t *rv_plic) {
  if (rv_plic == NULL || dt == NULL) {
    return kDifBadArg;
  }

  rv_plic->base_addr =
      mmio_region_from_addr(dt_rv_plic_reg_block(dt, kDtRvPlicRegBlockDefault));

  return kDifOk;
}

dif_result_t dif_rv_plic_alert_force(const dif_rv_plic_t *rv_plic,
                                     dif_rv_plic_alert_t alert) {
  if (rv_plic == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t alert_idx;
  switch (alert) {
    case kDifRvPlicAlertFatalFault:
      alert_idx = RV_PLIC_ALERT_TEST_FATAL_FAULT_BIT;
      break;
    default:
      return kDifBadArg;
  }

  uint32_t alert_test_reg = bitfield_bit32_write(0, alert_idx, true);
  mmio_region_write32(rv_plic->base_addr,
                      (ptrdiff_t)RV_PLIC_ALERT_TEST_REG_OFFSET, alert_test_reg);

  return kDifOk;
}
