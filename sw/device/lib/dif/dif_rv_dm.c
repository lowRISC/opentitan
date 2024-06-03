// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_rv_dm.h"

#include "sw/device/lib/base/multibits.h"

#include "rv_dm_regs.h"  // Generated.

static bool late_debug_enable_is_locked(const dif_rv_dm_t *rv_dm) {
  uint32_t reg = mmio_region_read32(rv_dm->base_addr,
                                    RV_DM_LATE_DEBUG_ENABLE_REGWEN_REG_OFFSET);
  return !bitfield_bit32_read(
      reg, RV_DM_LATE_DEBUG_ENABLE_REGWEN_LATE_DEBUG_ENABLE_REGWEN_BIT);
}

dif_result_t dif_rv_dm_late_debug_configure(const dif_rv_dm_t *rv_dm,
                                            dif_toggle_t enable) {
  if (rv_dm == NULL || !dif_is_valid_toggle(enable)) {
    return kDifBadArg;
  }

  if (late_debug_enable_is_locked(rv_dm)) {
    return kDifLocked;
  }

  multi_bit_bool_t enable_value = kMultiBitBool32False;
  if (enable == kDifToggleEnabled) {
    enable_value = kMultiBitBool32True;
  }

  mmio_region_write32(rv_dm->base_addr, RV_DM_LATE_DEBUG_ENABLE_REG_OFFSET,
                      enable_value);

  return kDifOk;
}

dif_result_t dif_rv_dm_late_debug_lock(const dif_rv_dm_t *rv_dm) {
  if (rv_dm == NULL) {
    return kDifBadArg;
  }
  mmio_region_write32(
      rv_dm->base_addr, RV_DM_LATE_DEBUG_ENABLE_REGWEN_REG_OFFSET,
      bitfield_bit32_write(
          0, RV_DM_LATE_DEBUG_ENABLE_REGWEN_LATE_DEBUG_ENABLE_REGWEN_BIT,
          false));
  return kDifOk;
}

dif_result_t dif_rv_dm_late_debug_is_locked(const dif_rv_dm_t *rv_dm,
                                            bool *is_locked) {
  if (rv_dm == NULL || is_locked == NULL) {
    return kDifBadArg;
  }

  *is_locked = late_debug_enable_is_locked(rv_dm);
  return kDifOk;
}
