// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_rstmgr.h"

#include <stdint.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/mmio.h"
#include "rstmgr_regs.h"  // Generated.

// This macro simplifies the `_Static_assert` check to make sure that the
// public reset info register bitfield matches register bits.
#define RSTMGR_RESET_INFO_CHECK(pub_name, priv_name)                      \
  _Static_assert(                                                         \
      kDifRstmgrResetInfo##pub_name == (0x1 << RSTMGR_RESET_##priv_name), \
      "kDifRstmgrResetInfo" #pub_name " must match the register definition!")

RSTMGR_RESET_INFO_CHECK(Por, INFO_POR);
RSTMGR_RESET_INFO_CHECK(LowPowerExit, INFO_LOW_POWER_EXIT);
RSTMGR_RESET_INFO_CHECK(Ndm, INFO_NDM_RESET);
RSTMGR_RESET_INFO_CHECK(HwReq, INFO_HW_REQ);

_Static_assert(kDifRstmgrResetInfoLast == kDifRstmgrResetInfoHwReq,
               "Please add `RSTMGR_RESET_INFO_CHECK` for the new reset type!");

_Static_assert(
    RSTMGR_PARAM_NUMSWRESETS == 2,
    "Number of software resets has changed, please update this file!");

// The Reset Manager implementation will have to be updated if the number
// of software resets grows, as it would span across multiple registers, so
// there will be multiple of Reset Enable and Reset Control registers. The
// appropriate offset from the peripheral base would then have to be
// calculated.
_Static_assert(
    RSTMGR_PARAM_NUMSWRESETS <= 32,
    "Reset Enable and Control registers span across multiple registers!");

/**
 * Checks whether the software reset is disabled for a `peripheral`.
 */
static bool rstmgr_software_reset_is_locked(
    mmio_region_t base_addr, dif_rstmgr_peripheral_t peripheral) {
  uint32_t bitfield =
      mmio_region_read32(base_addr, RSTMGR_SW_RST_REGEN_REG_OFFSET);

  // When bit is cleared, the software reset for `peripheral` is disabled.
  return !bitfield_bit32_read(bitfield, peripheral);
}

/**
 * Holds or releases a `peripheral` in/from the reset state.
 */
static void rstmgr_software_reset_hold(mmio_region_t base_addr,
                                       dif_rstmgr_peripheral_t peripheral,
                                       bool hold) {
  uint32_t bitfield =
      mmio_region_read32(base_addr, RSTMGR_SW_RST_CTRL_N_REG_OFFSET);

  // Clear bit to hold a `peripheral` in the reset state, and set
  bool bit = hold ? false : true;
  bitfield = bitfield_bit32_write(bitfield, peripheral, bit);

  mmio_region_write32(base_addr, RSTMGR_SW_RST_CTRL_N_REG_OFFSET, bitfield);
}

/**
 * Clears entire reset info register.
 *
 * Normal "Power On Reset" cause is also cleared. Set bit to clear.
 */
static void rstmgr_reset_info_clear(mmio_region_t base_addr) {
  mmio_region_write32(base_addr, RSTMGR_RESET_INFO_REG_OFFSET, UINT32_MAX);
}

dif_rstmgr_result_t dif_rstmgr_init(dif_rstmgr_params_t params,
                                    dif_rstmgr_t *handle) {
  if (handle == NULL) {
    return kDifRstmgrBadArg;
  }

  handle->params = params;

  return kDifRstmgrOk;
}

dif_rstmgr_result_t dif_rstmgr_reset(const dif_rstmgr_t *handle) {
  if (handle == NULL) {
    return kDifRstmgrBadArg;
  }

  mmio_region_t base_addr = handle->params.base_addr;

  rstmgr_reset_info_clear(base_addr);

  // Set bits to stop holding all peripherals in the reset state.
  mmio_region_write32(base_addr, RSTMGR_SW_RST_CTRL_N_REG_OFFSET, UINT32_MAX);

  return kDifRstmgrOk;
}

dif_rstmgr_result_t dif_rstmgr_reset_lock(const dif_rstmgr_t *handle,
                                          dif_rstmgr_peripheral_t peripheral) {
  if (handle == NULL || peripheral >= RSTMGR_PARAM_NUMSWRESETS) {
    return kDifRstmgrBadArg;
  }

  mmio_region_t base_addr = handle->params.base_addr;

  // Clear bit to disable the software reset for the peripheral.
  uint32_t bitfield = bitfield_bit32_write(UINT32_MAX, peripheral, false);

  mmio_region_write32(base_addr, RSTMGR_SW_RST_REGEN_REG_OFFSET, bitfield);

  return kDifRstmgrOk;
}

dif_rstmgr_result_t dif_rstmgr_reset_is_locked(
    const dif_rstmgr_t *handle, dif_rstmgr_peripheral_t peripheral,
    bool *is_locked) {
  if (handle == NULL || is_locked == NULL ||
      peripheral >= RSTMGR_PARAM_NUMSWRESETS) {
    return kDifRstmgrBadArg;
  }

  mmio_region_t base_addr = handle->params.base_addr;
  *is_locked = rstmgr_software_reset_is_locked(base_addr, peripheral);

  return kDifRstmgrOk;
}

dif_rstmgr_result_t dif_rstmgr_reset_info_get(
    const dif_rstmgr_t *handle, dif_rstmgr_reset_info_bitfield_t *info) {
  if (handle == NULL || info == NULL) {
    return kDifRstmgrBadArg;
  }

  mmio_region_t base_addr = handle->params.base_addr;
  *info = mmio_region_read32(base_addr, RSTMGR_RESET_INFO_REG_OFFSET);

  return kDifRstmgrOk;
}

dif_rstmgr_result_t dif_rstmgr_reset_info_clear(const dif_rstmgr_t *handle) {
  if (handle == NULL) {
    return kDifRstmgrBadArg;
  }

  mmio_region_t base_addr = handle->params.base_addr;

  rstmgr_reset_info_clear(base_addr);

  return kDifRstmgrOk;
}

dif_rstmgr_software_reset_result_t dif_rstmgr_software_reset(
    const dif_rstmgr_t *handle, dif_rstmgr_peripheral_t peripheral,
    dif_rstmgr_software_reset_t reset) {
  if (handle == NULL || peripheral >= RSTMGR_PARAM_NUMSWRESETS) {
    return kDifRstmgrSoftwareResetBadArg;
  }

  mmio_region_t base_addr = handle->params.base_addr;
  if (rstmgr_software_reset_is_locked(base_addr, peripheral)) {
    return kDifRstmgrSoftwareResetLocked;
  }

  switch (reset) {
    case kDifRstmgrSoftwareReset:
      rstmgr_software_reset_hold(base_addr, peripheral, true);
      rstmgr_software_reset_hold(base_addr, peripheral, false);
      break;
    case kDifRstmgrSoftwareResetHold:
      rstmgr_software_reset_hold(base_addr, peripheral, true);
      break;
    case kDifRstmgrSoftwareResetRelease:
      rstmgr_software_reset_hold(base_addr, peripheral, false);
      break;
    default:
      return kDifRstmgrSoftwareResetError;
  }

  return kDifRstmgrSoftwareResetOk;
}

dif_rstmgr_result_t dif_rstmgr_software_reset_is_held(
    const dif_rstmgr_t *handle, dif_rstmgr_peripheral_t peripheral,
    bool *asserted) {
  if (handle == NULL || asserted == NULL ||
      peripheral >= RSTMGR_PARAM_NUMSWRESETS) {
    return kDifRstmgrBadArg;
  }

  mmio_region_t base_addr = handle->params.base_addr;

  uint32_t bitfield =
      mmio_region_read32(base_addr, RSTMGR_SW_RST_CTRL_N_REG_OFFSET);

  // When the bit is cleared - peripheral is held in reset.
  *asserted = !bitfield_bit32_read(bitfield, peripheral);

  return kDifRstmgrOk;
}
