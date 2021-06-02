// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/silicon_creator/lib/base/abs_mmio.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "rstmgr_regs.h"

enum {
  kBase = TOP_EARLGREY_RSTMGR_AON_BASE_ADDR,
};

rstmgr_alert_info_t rstmgr_alert_info;

static void rstmgr_alert_info_collect(void) {
  rstmgr_alert_info.length = bitfield_field32_read(
      abs_mmio_read32(kBase + RSTMGR_ALERT_INFO_ATTR_REG_OFFSET),
      RSTMGR_ALERT_INFO_ATTR_CNT_AVAIL_FIELD);
  for (uint32_t i = 0; i < rstmgr_alert_info.length; ++i) {
    abs_mmio_write32(
        kBase + RSTMGR_ALERT_INFO_CTRL_REG_OFFSET,
        bitfield_field32_write(0, RSTMGR_ALERT_INFO_CTRL_INDEX_FIELD, i));
    rstmgr_alert_info.info[i] =
        abs_mmio_read32(kBase + RSTMGR_ALERT_INFO_REG_OFFSET);
  }
}

uint32_t rstmgr_reason_get(void) {
  rstmgr_alert_info_collect();
  return abs_mmio_read32(kBase + RSTMGR_RESET_INFO_REG_OFFSET);
}

void rstmgr_alert_info_enable(void) {
  abs_mmio_write32(kBase + RSTMGR_ALERT_INFO_CTRL_REG_OFFSET, 1);
}
