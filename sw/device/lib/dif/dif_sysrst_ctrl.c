// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_sysrst_ctrl.h"

#include <assert.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/dif/dif_base.h"

#include "sysrst_ctrl_regs.h"  // Generated.

dif_result_t dif_sysrst_ctrl_key_combo_detect_configure(
    const dif_sysrst_ctrl_t *sysrst_ctrl, dif_sysrst_ctrl_key_combo_t key_combo,
    dif_sysrst_ctrl_key_combo_config_t config) {
  if (sysrst_ctrl == NULL || config.keys > kDifSysrstCtrlKeyAll ||
      config.actions > kDifSysrstCtrlKeyComboActionAll) {
    return kDifBadArg;
  }

  ptrdiff_t combo_select_ctl_reg_offset;
  ptrdiff_t combo_detect_ctl_reg_offset;
  ptrdiff_t combo_action_ctl_reg_offset;

  switch (key_combo) {
    case kDifSysrstCtrlKeyCombo0:
      combo_select_ctl_reg_offset = SYSRST_CTRL_COM_SEL_CTL_0_REG_OFFSET;
      combo_detect_ctl_reg_offset = SYSRST_CTRL_COM_DET_CTL_0_REG_OFFSET;
      combo_action_ctl_reg_offset = SYSRST_CTRL_COM_OUT_CTL_0_REG_OFFSET;
      break;
    case kDifSysrstCtrlKeyCombo1:
      combo_select_ctl_reg_offset = SYSRST_CTRL_COM_SEL_CTL_1_REG_OFFSET;
      combo_detect_ctl_reg_offset = SYSRST_CTRL_COM_DET_CTL_1_REG_OFFSET;
      combo_action_ctl_reg_offset = SYSRST_CTRL_COM_OUT_CTL_1_REG_OFFSET;
      break;
    case kDifSysrstCtrlKeyCombo2:
      combo_select_ctl_reg_offset = SYSRST_CTRL_COM_SEL_CTL_2_REG_OFFSET;
      combo_detect_ctl_reg_offset = SYSRST_CTRL_COM_DET_CTL_2_REG_OFFSET;
      combo_action_ctl_reg_offset = SYSRST_CTRL_COM_OUT_CTL_2_REG_OFFSET;
      break;
    case kDifSysrstCtrlKeyCombo3:
      combo_select_ctl_reg_offset = SYSRST_CTRL_COM_SEL_CTL_3_REG_OFFSET;
      combo_detect_ctl_reg_offset = SYSRST_CTRL_COM_DET_CTL_3_REG_OFFSET;
      combo_action_ctl_reg_offset = SYSRST_CTRL_COM_OUT_CTL_3_REG_OFFSET;
      break;
    default:
      return kDifBadArg;
  }

  if (!mmio_region_read32(sysrst_ctrl->base_addr,
                          SYSRST_CTRL_REGWEN_REG_OFFSET)) {
    return kDifLocked;
  }

  mmio_region_write32(sysrst_ctrl->base_addr, combo_select_ctl_reg_offset,
                      config.keys);
  mmio_region_write32(sysrst_ctrl->base_addr, combo_detect_ctl_reg_offset,
                      config.detection_time_threshold);
  mmio_region_write32(sysrst_ctrl->base_addr, combo_action_ctl_reg_offset,
                      config.actions);

  if (config.actions & kDifSysrstCtrlKeyComboActionEcReset) {
    mmio_region_write32(sysrst_ctrl->base_addr,
                        SYSRST_CTRL_EC_RST_CTL_REG_OFFSET,
                        config.embedded_controller_reset_duration);
  }

  return kDifOk;
}
