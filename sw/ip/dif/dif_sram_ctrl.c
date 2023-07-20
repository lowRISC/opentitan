// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_sram_ctrl.h"

#include "sw/device/lib/base/multibits.h"

#include "sram_ctrl_regs.h"  // Generated.

/**
 * Obtains the lock state of the "Control" register.
 *
 * When locked, new scrambling key and SRAM pseudo-random data overwriting
 * requests are not available.
 */
static bool sram_ctrl_locked_ctrl(const dif_sram_ctrl_t *sram_ctrl) {
  return mmio_region_read32(sram_ctrl->base_addr,
                            SRAM_CTRL_CTRL_REGWEN_REG_OFFSET)
             ? false
             : true;
}

/**
 * Obtains the lock state of the "Exec enable" register.
 *
 * When locked, execution from SRAM is disabled, and an attempt to do so
 * will result in an access violation.
 */
static bool sram_ctrl_exec_locked(const dif_sram_ctrl_t *sram_ctrl) {
  return mmio_region_read32(sram_ctrl->base_addr,
                            SRAM_CTRL_EXEC_REGWEN_REG_OFFSET)
             ? false
             : true;
}

/**
 * Locks SRAM Controller "Control" functionality.
 *
 * SRAM Scrambling and RAM wiping is no longer available.
 */
static void sram_ctrl_lock_ctrl(const dif_sram_ctrl_t *sram_ctrl) {
  mmio_region_write32(sram_ctrl->base_addr, SRAM_CTRL_CTRL_REGWEN_REG_OFFSET,
                      0);
}

/**
 * Locks SRAM Controller "Execute" functionality.
 *
 * Execution from SRAM cannot be changed (when enabled - it stays enabled, and
 * vice versa).
 */
static void sram_ctrl_lock_exec(const dif_sram_ctrl_t *sram_ctrl) {
  mmio_region_write32(sram_ctrl->base_addr, SRAM_CTRL_EXEC_REGWEN_REG_OFFSET,
                      0);
}

/**
 * Obtains the SRAM Controller statues.
 *
 * `dif_sram_ctrl_status_t` can be used to query individual flags.
 */
static uint32_t sram_ctrl_get_status(const dif_sram_ctrl_t *sram_ctrl) {
  return mmio_region_read32(sram_ctrl->base_addr, SRAM_CTRL_STATUS_REG_OFFSET);
}

dif_result_t dif_sram_ctrl_scramble(const dif_sram_ctrl_t *sram_ctrl) {
  if (sram_ctrl == NULL) {
    return kDifBadArg;
  }

  if (sram_ctrl_locked_ctrl(sram_ctrl)) {
    return kDifLocked;
  }

  // Issue request for new scrambling key.
  uint32_t reg =
      bitfield_bit32_write(0, SRAM_CTRL_CTRL_RENEW_SCR_KEY_BIT, true);
  mmio_region_write32(sram_ctrl->base_addr, SRAM_CTRL_CTRL_REG_OFFSET, reg);

  // Wait until the scrambling key has been updated.
  dif_sram_ctrl_status_bitfield_t status;
  do {
    status = sram_ctrl_get_status(sram_ctrl);
  } while ((status & kDifSramCtrlStatusScrKeyValid) == 0);

  // Overwrite memory with pseudo random data.
  reg = bitfield_bit32_write(0, SRAM_CTRL_CTRL_INIT_BIT, true);
  mmio_region_write32(sram_ctrl->base_addr, SRAM_CTRL_CTRL_REG_OFFSET, reg);

  // Wait for memory to be overwritten with pseudo random data.
  do {
    status = sram_ctrl_get_status(sram_ctrl);
  } while ((status & kDifSramCtrlStatusInitDone) == 0);

  // Check for the errors during memory overwriting.
  return (status & kDifSramCtrlStatusInitErr) == 0 ? kDifOk : kDifError;
}

dif_result_t dif_sram_ctrl_request_new_key(const dif_sram_ctrl_t *sram_ctrl) {
  if (sram_ctrl == NULL) {
    return kDifBadArg;
  }

  if (sram_ctrl_locked_ctrl(sram_ctrl)) {
    return kDifLocked;
  }

  uint32_t reg =
      bitfield_bit32_write(0, SRAM_CTRL_CTRL_RENEW_SCR_KEY_BIT, true);
  mmio_region_write32(sram_ctrl->base_addr, SRAM_CTRL_CTRL_REG_OFFSET, reg);

  return kDifOk;
}

dif_result_t dif_sram_ctrl_wipe(const dif_sram_ctrl_t *sram_ctrl) {
  if (sram_ctrl == NULL) {
    return kDifBadArg;
  }

  if (sram_ctrl_locked_ctrl(sram_ctrl)) {
    return kDifLocked;
  }

  uint32_t reg = bitfield_bit32_write(0, SRAM_CTRL_CTRL_INIT_BIT, true);
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

dif_result_t dif_sram_ctrl_exec_get_enabled(const dif_sram_ctrl_t *sram_ctrl,
                                            dif_toggle_t *state) {
  if (sram_ctrl == NULL || state == NULL) {
    return kDifBadArg;
  }

  uint32_t reg =
      mmio_region_read32(sram_ctrl->base_addr, SRAM_CTRL_EXEC_REG_OFFSET);

  *state = (reg == kMultiBitBool4True) ? kDifToggleEnabled : kDifToggleDisabled;

  return kDifOk;
}

dif_result_t dif_sram_ctrl_exec_set_enabled(const dif_sram_ctrl_t *sram_ctrl,
                                            dif_toggle_t state) {
  if (sram_ctrl == NULL) {
    return kDifBadArg;
  }

  if (sram_ctrl_exec_locked(sram_ctrl)) {
    return kDifLocked;
  }

  uint32_t value =
      (state == kDifToggleEnabled) ? kMultiBitBool4True : kMultiBitBool4False;
  mmio_region_write32(sram_ctrl->base_addr, SRAM_CTRL_EXEC_REG_OFFSET, value);

  return kDifOk;
}

dif_result_t dif_sram_ctrl_lock(const dif_sram_ctrl_t *sram_ctrl,
                                dif_sram_ctrl_lock_t lock) {
  if (sram_ctrl == NULL) {
    return kDifBadArg;
  }

  switch (lock) {
    case kDifSramCtrlLockCtrl:
      sram_ctrl_lock_ctrl(sram_ctrl);
      break;
    case kDifSramCtrlLockExec:
      sram_ctrl_lock_exec(sram_ctrl);
      break;
    default:
      return kDifError;
  }

  return kDifOk;
}

dif_result_t dif_sram_ctrl_is_locked(const dif_sram_ctrl_t *sram_ctrl,
                                     dif_sram_ctrl_lock_t lock,
                                     bool *is_locked) {
  if (sram_ctrl == NULL || is_locked == NULL) {
    return kDifBadArg;
  }

  switch (lock) {
    case kDifSramCtrlLockCtrl:
      *is_locked = sram_ctrl_locked_ctrl(sram_ctrl);
      break;
    case kDifSramCtrlLockExec:
      *is_locked = sram_ctrl_exec_locked(sram_ctrl);
      break;
    default:
      return kDifError;
  }

  return kDifOk;
}
