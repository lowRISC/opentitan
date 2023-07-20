// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/device/lib/dif/autogen/dif_rstmgr_autogen.h"

#include <stdint.h>

#include "sw/device/lib/dif/dif_base.h"

#include "rstmgr_regs.h"  // Generated.

OT_WARN_UNUSED_RESULT
dif_result_t dif_rstmgr_init(mmio_region_t base_addr, dif_rstmgr_t *rstmgr) {
  if (rstmgr == NULL) {
    return kDifBadArg;
  }

  rstmgr->base_addr = base_addr;

  return kDifOk;
}

dif_result_t dif_rstmgr_alert_force(const dif_rstmgr_t *rstmgr,
                                    dif_rstmgr_alert_t alert) {
  if (rstmgr == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t alert_idx;
  switch (alert) {
    case kDifRstmgrAlertFatalFault:
      alert_idx = RSTMGR_ALERT_TEST_FATAL_FAULT_BIT;
      break;
    case kDifRstmgrAlertFatalCnstyFault:
      alert_idx = RSTMGR_ALERT_TEST_FATAL_CNSTY_FAULT_BIT;
      break;
    default:
      return kDifBadArg;
  }

  uint32_t alert_test_reg = bitfield_bit32_write(0, alert_idx, true);
  mmio_region_write32(rstmgr->base_addr,
                      (ptrdiff_t)RSTMGR_ALERT_TEST_REG_OFFSET, alert_test_reg);

  return kDifOk;
}
