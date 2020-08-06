// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_rstmgr.h"

#include <stdint.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/mmio.h"
#include "rstmgr_regs.h"  // Generated.

_Static_assert(kDifRstmgrCausePowerOn == RSTMGR_RESET_INFO_CAUSE_POR,
               "kDifRstmgrCausePowerOn must match the register definition!");
_Static_assert(
    kDifRstmgrCauseLowPowerExit == RSTMGR_RESET_INFO_CAUSE_LOW_POWER_EXIT,
    "kDifRstmgrCauseLowPowerExit must match the register definition!");
_Static_assert(kDifRstmgrCauseWatchdog == RSTMGR_RESET_INFO_CAUSE_WATCHDOG,
               "kDifRstmgrCauseWatchdog must match the register definition!");
_Static_assert(
    kDifRstmgrCauseSecurityEscalation == RSTMGR_RESET_INFO_CAUSE_ESCALATION,
    "kDifRstmgrCauseSecurityEscalation must match the register definition!");
_Static_assert(
    kDifRstmgrCauseNonDebugModuleRequest ==
        RSTMGR_RESET_INFO_CAUSE_NON_DEBUG_MODULE,
    "kDifRstmgrCauseNonDebugModuleRequest must match the register definition!");

_Static_assert(RSTMGR_SPI_DEVICE_REGEN_SPI_DEVICE_REGEN ==
                   RSTMGR_USB_REGEN_USB_REGEN,
               "SPI and USB regen bit offsets are not the same");
_Static_assert(RSTMGR_RST_SPI_DEVICE_N_RST_SPI_DEVICE_N ==
                   RSTMGR_RST_USB_N_RST_USB_N,
               "SPI and USB reset bit offsets are not the same");

#define RSTMGR_REGEN_BIT_OFFSET RSTMGR_SPI_DEVICE_REGEN_SPI_DEVICE_REGEN
#define RSTMGR_RESET_BIT_OFFSET RSTMGR_RST_SPI_DEVICE_N_RST_SPI_DEVICE_N

static const bitfield_field32_t kRstmgrCausesField = {
    .mask = RSTMGR_RESET_INFO_CAUSE_MASK,
    .index = RSTMGR_RESET_INFO_CAUSE_OFFSET,
};

// Regen registers are "write 1 to clear" = write 1 to lock.
static const ptrdiff_t kRstmgrRegenOffsetsMap[] = {
        [kDifRstmgrPeripheralSpi] = RSTMGR_SPI_DEVICE_REGEN_REG_OFFSET,
        [kDifRstmgrPeripheralUsb] = RSTMGR_USB_REGEN_REG_OFFSET,
};

// Reset registers, when set to 0, peripheral is held in reset.
static const ptrdiff_t kRstmgrResetOffsetsMap[] = {
        [kDifRstmgrPeripheralSpi] = RSTMGR_RST_SPI_DEVICE_N_REG_OFFSET,
        [kDifRstmgrPeripheralUsb] = RSTMGR_RST_USB_N_REG_OFFSET,
};

// TODO - static assert to make sure that the above arrays cover all relevant
//        peripherals?

static void rstmgr_software_reset_hold(mmio_region_t base_addr,
                                       dif_rstmgr_peripheral_t peripheral) {
  ptrdiff_t reg_offset = kRstmgrResetOffsetsMap[peripheral];
  uint32_t bitfield = bitfield_bit32_write(0, RSTMGR_RESET_BIT_OFFSET, false);
  mmio_region_write32(base_addr, reg_offset, bitfield);
}

static bool rstmgr_software_reset_is_held(mmio_region_t base_addr,
                                          dif_rstmgr_peripheral_t peripheral) {
  ptrdiff_t reg_offset = kRstmgrResetOffsetsMap[peripheral];
  uint32_t bitfield = mmio_region_read32(base_addr, reg_offset);
  return !bitfield_bit32_read(bitfield, RSTMGR_RESET_BIT_OFFSET);
}

static void rstmgr_software_reset_release(mmio_region_t base_addr,
                                          dif_rstmgr_peripheral_t peripheral) {
  ptrdiff_t reg_offset = kRstmgrResetOffsetsMap[peripheral];
  uint32_t bitfield = bitfield_bit32_write(0, RSTMGR_RESET_BIT_OFFSET, true);
  mmio_region_write32(base_addr, reg_offset, bitfield);
}

static void rstmgr_software_reset_lock(mmio_region_t base_addr,
                                       dif_rstmgr_peripheral_t peripheral) {
  ptrdiff_t reg_offset = kRstmgrRegenOffsetsMap[peripheral];
  uint32_t bitfield = bitfield_bit32_write(0, RSTMGR_REGEN_BIT_OFFSET, true);
  mmio_region_write32(base_addr, reg_offset, bitfield);
}

static bool rstmgr_software_reset_locked(mmio_region_t base_addr,
                                         dif_rstmgr_peripheral_t peripheral) {
  ptrdiff_t reg_offset = kRstmgrRegenOffsetsMap[peripheral];
  uint32_t bitfield = mmio_region_read32(base_addr, reg_offset);
  return !bitfield_bit32_read(bitfield, RSTMGR_REGEN_BIT_OFFSET);
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

  // Clear the info register (normal "Power On Reset" cause is also cleared).
  mmio_region_write32(base_addr, RSTMGR_RESET_INFO_REG_OFFSET, UINT32_MAX);

  // De-assert software resets.
  for (dif_rstmgr_peripheral_t i = 0; i <= kDifRstmgrPeripheralLast; ++i) {
    rstmgr_software_reset_release(base_addr, i);
  }

  return kDifRstmgrOk;
}

dif_rstmgr_result_t dif_rstmgr_reset_lock(const dif_rstmgr_t *handle,
                                          dif_rstmgr_peripheral_t peripheral) {
  if (handle == NULL) {
    return kDifRstmgrBadArg;
  }

  mmio_region_t base_addr = handle->params.base_addr;
  rstmgr_software_reset_lock(base_addr, peripheral);

  return kDifRstmgrOk;
}

dif_rstmgr_result_t dif_rstmgr_reset_is_locked(
    const dif_rstmgr_t *handle, dif_rstmgr_peripheral_t peripheral,
    bool *is_locked) {
  if (handle == NULL || is_locked == NULL) {
    return kDifRstmgrBadArg;
  }

  mmio_region_t base_addr = handle->params.base_addr;
  *is_locked = rstmgr_software_reset_locked(base_addr, peripheral);

  return kDifRstmgrOk;
}

dif_rstmgr_result_t dif_rstmgr_causes_get(
    const dif_rstmgr_t *handle, dif_rstmgr_causes_bitfield_t *causes) {
  if (handle == NULL || causes == NULL) {
    return kDifRstmgrBadArg;
  }

  mmio_region_t base_addr = handle->params.base_addr;
  uint32_t reg = mmio_region_read32(base_addr, RSTMGR_RESET_INFO_REG_OFFSET);

  *causes = bitfield_field32_read(reg, kRstmgrCausesField);

  return kDifRstmgrOk;
}

dif_rstmgr_result_t dif_rstmgr_causes_clear(const dif_rstmgr_t *handle) {
  if (handle == NULL) {
    return kDifRstmgrBadArg;
  }

  mmio_region_t base_addr = handle->params.base_addr;
  uint32_t reg = mmio_region_read32(base_addr, RSTMGR_RESET_INFO_REG_OFFSET);

  reg = bitfield_field32_write(reg, kRstmgrCausesField,
                               RSTMGR_RESET_INFO_CAUSE_MASK);

  mmio_region_write32(base_addr, RSTMGR_RESET_INFO_REG_OFFSET, reg);

  return kDifRstmgrOk;
}

dif_rstmgr_result_t dif_rstmgr_software_reset(
    const dif_rstmgr_t *handle, dif_rstmgr_peripheral_t peripheral,
    dif_rstmgr_software_reset_t reset) {
  if (handle == NULL) {
    return kDifRstmgrBadArg;
  }

  mmio_region_t base_addr = handle->params.base_addr;
  if (rstmgr_software_reset_locked(base_addr, peripheral)) {
    return kDifRstmgrLocked;
  }

  switch (reset) {
    case kDifRstmgrSoftwareReset:
      rstmgr_software_reset_hold(base_addr, peripheral);
      rstmgr_software_reset_release(base_addr, peripheral);
      break;
    case kDifRstmgrSoftwareResetHold:
      rstmgr_software_reset_hold(base_addr, peripheral);
      break;
    case kDifRstmgrSoftwareResetRelease:
      rstmgr_software_reset_release(base_addr, peripheral);
      break;
    default:
      return kDifRstmgrError;
  }

  return kDifRstmgrOk;
}

dif_rstmgr_result_t dif_rstmgr_software_reset_is_held(
    const dif_rstmgr_t *handle, dif_rstmgr_peripheral_t peripheral,
    bool *asserted) {
  if (handle == NULL || asserted == NULL) {
    return kDifRstmgrBadArg;
  }

  mmio_region_t base_addr = handle->params.base_addr;
  *asserted = rstmgr_software_reset_is_held(base_addr, peripheral);

  return kDifRstmgrOk;
}
