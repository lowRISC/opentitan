// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/device/lib/dif/autogen/dif_rv_core_ibex_autogen.h"

#include <stdint.h>

#include "sw/device/lib/dif/dif_base.h"

#include "rv_core_ibex_regs.h"  // Generated.

OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_core_ibex_init(mmio_region_t base_addr,
                                   dif_rv_core_ibex_t *rv_core_ibex) {
  if (rv_core_ibex == NULL) {
    return kDifBadArg;
  }

  rv_core_ibex->base_addr = base_addr;

  return kDifOk;
}

dif_result_t dif_rv_core_ibex_alert_force(
    const dif_rv_core_ibex_t *rv_core_ibex, dif_rv_core_ibex_alert_t alert) {
  if (rv_core_ibex == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t alert_idx;
  switch (alert) {
    case kDifRvCoreIbexAlertFatalSwErr:
      alert_idx = RV_CORE_IBEX_ALERT_TEST_FATAL_SW_ERR_BIT;
      break;
    case kDifRvCoreIbexAlertRecovSwErr:
      alert_idx = RV_CORE_IBEX_ALERT_TEST_RECOV_SW_ERR_BIT;
      break;
    case kDifRvCoreIbexAlertFatalHwErr:
      alert_idx = RV_CORE_IBEX_ALERT_TEST_FATAL_HW_ERR_BIT;
      break;
    case kDifRvCoreIbexAlertRecovHwErr:
      alert_idx = RV_CORE_IBEX_ALERT_TEST_RECOV_HW_ERR_BIT;
      break;
    default:
      return kDifBadArg;
  }

  uint32_t alert_test_reg = bitfield_bit32_write(0, alert_idx, true);
  mmio_region_write32(rv_core_ibex->base_addr,
                      (ptrdiff_t)RV_CORE_IBEX_ALERT_TEST_REG_OFFSET,
                      alert_test_reg);

  return kDifOk;
}
