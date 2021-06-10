// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/alert.h"

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/base/abs_mmio.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "alert_handler_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

enum {
  kBase = TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR,
};

rom_error_t alert_configure(size_t index, alert_class_t cls,
                            alert_enable_t enabled) {
  if (index >= ALERT_HANDLER_ALERT_CLASS_MULTIREG_COUNT) {
    return kErrorAlertBadIndex;
  }
  index *= 4;

  switch (cls) {
    case kAlertClassA:
      abs_mmio_write32(kBase + ALERT_HANDLER_ALERT_CLASS_0_REG_OFFSET + index,
                       ALERT_HANDLER_ALERT_CLASS_0_CLASS_A_0_VALUE_CLASSA);
      break;
    case kAlertClassB:
      abs_mmio_write32(kBase + ALERT_HANDLER_ALERT_CLASS_0_REG_OFFSET + index,
                       ALERT_HANDLER_ALERT_CLASS_0_CLASS_A_0_VALUE_CLASSB);
      break;
    case kAlertClassC:
      abs_mmio_write32(kBase + ALERT_HANDLER_ALERT_CLASS_0_REG_OFFSET + index,
                       ALERT_HANDLER_ALERT_CLASS_0_CLASS_A_0_VALUE_CLASSC);
      break;
    case kAlertClassD:
      abs_mmio_write32(kBase + ALERT_HANDLER_ALERT_CLASS_0_REG_OFFSET + index,
                       ALERT_HANDLER_ALERT_CLASS_0_CLASS_A_0_VALUE_CLASSD);
      break;
    case kAlertClassX:
      return kErrorOk;
    default:
      return kErrorAlertBadClass;
  }

  switch (enabled) {
    case kAlertEnableNone:
      break;
    case kAlertEnableLocked:
      // Enable, then lock.
      abs_mmio_write32(kBase + ALERT_HANDLER_ALERT_EN_0_REG_OFFSET + index, 1);
      abs_mmio_write32(kBase + ALERT_HANDLER_ALERT_REGWEN_0_REG_OFFSET + index,
                       0);
      break;
    case kAlertEnableEnabled:
      abs_mmio_write32(kBase + ALERT_HANDLER_ALERT_EN_0_REG_OFFSET + index, 1);
      break;
    default:
      return kErrorAlertBadEnable;
  }

  return kErrorOk;
}

rom_error_t alert_local_configure(size_t index, alert_class_t cls,
                                  alert_enable_t enabled) {
  if (index >= ALERT_HANDLER_LOC_ALERT_CLASS_MULTIREG_COUNT) {
    return kErrorAlertBadIndex;
  }
  index *= 4;

  switch (cls) {
    case kAlertClassA:
      abs_mmio_write32(
          kBase + ALERT_HANDLER_LOC_ALERT_CLASS_0_REG_OFFSET + index,
          ALERT_HANDLER_LOC_ALERT_CLASS_0_CLASS_LA_0_VALUE_CLASSA);
      break;
    case kAlertClassB:
      abs_mmio_write32(
          kBase + ALERT_HANDLER_LOC_ALERT_CLASS_0_REG_OFFSET + index,
          ALERT_HANDLER_LOC_ALERT_CLASS_0_CLASS_LA_0_VALUE_CLASSB);
      break;
    case kAlertClassC:
      abs_mmio_write32(
          kBase + ALERT_HANDLER_LOC_ALERT_CLASS_0_REG_OFFSET + index,
          ALERT_HANDLER_LOC_ALERT_CLASS_0_CLASS_LA_0_VALUE_CLASSC);
      break;
    case kAlertClassD:
      abs_mmio_write32(
          kBase + ALERT_HANDLER_LOC_ALERT_CLASS_0_REG_OFFSET + index,
          ALERT_HANDLER_LOC_ALERT_CLASS_0_CLASS_LA_0_VALUE_CLASSD);
      break;
    case kAlertClassX:
      return kErrorOk;
    default:
      return kErrorAlertBadClass;
  }

  switch (enabled) {
    case kAlertEnableNone:
      break;
    case kAlertEnableLocked:
      // Enable, then lock.
      abs_mmio_write32(kBase + ALERT_HANDLER_LOC_ALERT_EN_0_REG_OFFSET + index,
                       1);
      abs_mmio_write32(
          kBase + ALERT_HANDLER_LOC_ALERT_REGWEN_0_REG_OFFSET + index, 0);
      break;
    case kAlertEnableEnabled:
      abs_mmio_write32(kBase + ALERT_HANDLER_LOC_ALERT_EN_0_REG_OFFSET + index,
                       1);
      break;
    default:
      return kErrorAlertBadEnable;
  }

  return kErrorOk;
}

rom_error_t alert_class_configure(alert_class_t cls,
                                  const alert_class_config_t *config) {
  uint32_t offset = 0;
  uint32_t reg = 0;

  // Each escalation signal should be asserted in its corresponding phase.
  reg = bitfield_field32_write(reg, ALERT_HANDLER_CLASSA_CTRL_MAP_E0_FIELD, 0);
  reg = bitfield_field32_write(reg, ALERT_HANDLER_CLASSA_CTRL_MAP_E1_FIELD, 1);
  reg = bitfield_field32_write(reg, ALERT_HANDLER_CLASSA_CTRL_MAP_E2_FIELD, 2);
  reg = bitfield_field32_write(reg, ALERT_HANDLER_CLASSA_CTRL_MAP_E3_FIELD, 3);

  // All of the alert class register blocks are identical but at different
  // offsets.  We'll treat everything like Class A, but add in the offset
  // to the other classes.
  switch (cls) {
    case kAlertClassA:
      offset = ALERT_HANDLER_CLASSA_CTRL_REG_OFFSET -
               ALERT_HANDLER_CLASSA_CTRL_REG_OFFSET;
      break;
    case kAlertClassB:
      offset = ALERT_HANDLER_CLASSB_CTRL_REG_OFFSET -
               ALERT_HANDLER_CLASSA_CTRL_REG_OFFSET;
      break;
    case kAlertClassC:
      offset = ALERT_HANDLER_CLASSC_CTRL_REG_OFFSET -
               ALERT_HANDLER_CLASSA_CTRL_REG_OFFSET;
      break;
    case kAlertClassD:
      offset = ALERT_HANDLER_CLASSD_CTRL_REG_OFFSET -
               ALERT_HANDLER_CLASSA_CTRL_REG_OFFSET;
      break;
    case kAlertClassX:
    default:
      return kErrorAlertBadClass;
  }
  switch (config->enabled) {
    case kAlertEnableLocked:
      reg = bitfield_bit32_write(reg, ALERT_HANDLER_CLASSA_CTRL_LOCK_BIT, true);
      FALLTHROUGH_INTENDED;
    case kAlertEnableEnabled:
      reg = bitfield_bit32_write(reg, ALERT_HANDLER_CLASSA_CTRL_EN_BIT, true);
      FALLTHROUGH_INTENDED;
    case kAlertEnableNone:
      break;
    default:
      return kErrorAlertBadEnable;
  }
  switch (config->escalation) {
    case kAlertEscalatePhase3:
      reg =
          bitfield_bit32_write(reg, ALERT_HANDLER_CLASSA_CTRL_EN_E3_BIT, true);
      FALLTHROUGH_INTENDED;
    case kAlertEscalatePhase2:
      reg =
          bitfield_bit32_write(reg, ALERT_HANDLER_CLASSA_CTRL_EN_E2_BIT, true);
      FALLTHROUGH_INTENDED;
    case kAlertEscalatePhase1:
      reg =
          bitfield_bit32_write(reg, ALERT_HANDLER_CLASSA_CTRL_EN_E1_BIT, true);
      FALLTHROUGH_INTENDED;
    case kAlertEscalatePhase0:
      reg =
          bitfield_bit32_write(reg, ALERT_HANDLER_CLASSA_CTRL_EN_E0_BIT, true);
      FALLTHROUGH_INTENDED;
    case kAlertEscalateNone:
      break;
    default:
      return kErrorAlertBadEscalation;
  }

  abs_mmio_write32(kBase + ALERT_HANDLER_CLASSA_CTRL_REG_OFFSET + offset, reg);
  abs_mmio_write32(
      kBase + ALERT_HANDLER_CLASSA_ACCUM_THRESH_REG_OFFSET + offset,
      config->accum_threshold);
  abs_mmio_write32(kBase + ALERT_HANDLER_CLASSA_TIMEOUT_CYC_REG_OFFSET + offset,
                   config->timeout_cycles);
  for (size_t i = 0; i < 4; ++i) {
    abs_mmio_write32(
        kBase + ALERT_HANDLER_CLASSA_PHASE0_CYC_REG_OFFSET + offset + i * 4,
        config->phase_cycles[i]);
  }
  if (config->enabled == kAlertEnableLocked) {
    // Lock the alert configuration if it is configured to be locked.
    abs_mmio_write32(kBase + ALERT_HANDLER_CLASSA_REGWEN_REG_OFFSET + offset,
                     0);
  }
  return kErrorOk;
}

rom_error_t alert_ping_enable(void) {
  // Enable the ping timer, then lock it.
  abs_mmio_write32(kBase + ALERT_HANDLER_PING_TIMER_EN_REG_OFFSET, 1);
  abs_mmio_write32(kBase + ALERT_HANDLER_PING_TIMER_REGWEN_REG_OFFSET, 0);
  return kErrorOk;
}
