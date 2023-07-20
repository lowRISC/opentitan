// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

#include "sw/device/lib/dif/autogen/dif_lc_ctrl_autogen.h"

#include <stdint.h>

#include "sw/device/lib/dif/dif_base.h"

#include "lc_ctrl_regs.h"  // Generated.

OT_WARN_UNUSED_RESULT
dif_result_t dif_lc_ctrl_init(mmio_region_t base_addr, dif_lc_ctrl_t *lc_ctrl) {
  if (lc_ctrl == NULL) {
    return kDifBadArg;
  }

  lc_ctrl->base_addr = base_addr;

  return kDifOk;
}

dif_result_t dif_lc_ctrl_alert_force(const dif_lc_ctrl_t *lc_ctrl,
                                     dif_lc_ctrl_alert_t alert) {
  if (lc_ctrl == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t alert_idx;
  switch (alert) {
    case kDifLcCtrlAlertFatalProgError:
      alert_idx = LC_CTRL_ALERT_TEST_FATAL_PROG_ERROR_BIT;
      break;
    case kDifLcCtrlAlertFatalStateError:
      alert_idx = LC_CTRL_ALERT_TEST_FATAL_STATE_ERROR_BIT;
      break;
    case kDifLcCtrlAlertFatalBusIntegError:
      alert_idx = LC_CTRL_ALERT_TEST_FATAL_BUS_INTEG_ERROR_BIT;
      break;
    default:
      return kDifBadArg;
  }

  uint32_t alert_test_reg = bitfield_bit32_write(0, alert_idx, true);
  mmio_region_write32(lc_ctrl->base_addr,
                      (ptrdiff_t)LC_CTRL_ALERT_TEST_REG_OFFSET, alert_test_reg);

  return kDifOk;
}
