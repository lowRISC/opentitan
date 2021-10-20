// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_sram_ctrl.h"

#include "sram_ctrl_regs.h"  // Generated.

/**
 * Obtains the lock state of the "Control" register.
 *
 * When locked - new scrambling key and SRAM pseudo-random data overwriting
 * requests are not available.
 */
static dif_toggle_t sram_ctrl_lock_state(const dif_sram_ctrl_t *sram_ctrl) {
  return mmio_region_read32(sram_ctrl->base_addr,
                            SRAM_CTRL_CTRL_REGWEN_REG_OFFSET)
             ? kDifToggleDisabled
             : kDifToggleEnabled;
}

/**
 * Obtains the SRAM Controller statues.
 *
 * `dif_sram_ctrl_status_t` can be used to query individual flags.
 */
static uint32_t sram_ctrl_get_status(const dif_sram_ctrl_t *sram_ctrl) {
  return mmio_region_read32(sram_ctrl->base_addr, SRAM_CTRL_STATUS_REG_OFFSET);
}

dif_result_t dif_sram_ctrl_request_new_key(const dif_sram_ctrl_t *sram_ctrl) {
  if (sram_ctrl == NULL) {
    return kDifBadArg;
  }

  if (sram_ctrl_lock_state(sram_ctrl) == kDifToggleEnabled) {
    return kDifLocked;
  }

  uint32_t reg =
      bitfield_bit32_write(0, SRAM_CTRL_CTRL_RENEW_SCR_KEY_BIT, true);
  mmio_region_write32(sram_ctrl->base_addr, SRAM_CTRL_CTRL_REG_OFFSET, reg);

  return kDifOk;
}

dif_result_t dif_sram_ctrl_get_status(const dif_sram_ctrl_t *sram_ctrl,
                                      dif_sram_ctrl_status_bitfield_t *status) {
  if (sram_ctrl == NULL) {
    return kDifBadArg;
  }

  if (status == NULL) {
    return kDifBadArg;
  }

  *status = sram_ctrl_get_status(sram_ctrl);

  return kDifOk;
}
