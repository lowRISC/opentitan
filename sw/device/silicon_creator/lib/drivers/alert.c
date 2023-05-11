// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/alert.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/crc32.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "alert_handler_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"

enum {
  kBase = TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR,
};

rom_error_t alert_configure(size_t index, alert_class_t cls,
                            alert_enable_t enabled) {
  if (index >= ALERT_HANDLER_ALERT_CLASS_SHADOWED_MULTIREG_COUNT) {
    return kErrorAlertBadIndex;
  }
  index *= 4;

  switch (cls) {
    case kAlertClassA:
      abs_mmio_write32_shadowed(
          kBase + ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_REG_OFFSET + index,
          ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_CLASS_A_0_VALUE_CLASSA);
      break;
    case kAlertClassB:
      abs_mmio_write32_shadowed(
          kBase + ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_REG_OFFSET + index,
          ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_CLASS_A_0_VALUE_CLASSB);
      break;
    case kAlertClassC:
      abs_mmio_write32_shadowed(
          kBase + ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_REG_OFFSET + index,
          ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_CLASS_A_0_VALUE_CLASSC);
      break;
    case kAlertClassD:
      abs_mmio_write32_shadowed(
          kBase + ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_REG_OFFSET + index,
          ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_CLASS_A_0_VALUE_CLASSD);
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
      abs_mmio_write32_shadowed(
          kBase + ALERT_HANDLER_ALERT_EN_SHADOWED_0_REG_OFFSET + index, 1);
      abs_mmio_write32(kBase + ALERT_HANDLER_ALERT_REGWEN_0_REG_OFFSET + index,
                       0);
      break;
    case kAlertEnableEnabled:
      abs_mmio_write32_shadowed(
          kBase + ALERT_HANDLER_ALERT_EN_SHADOWED_0_REG_OFFSET + index, 1);
      break;
    default:
      return kErrorAlertBadEnable;
  }
  return kErrorOk;
}

rom_error_t alert_local_configure(size_t index, alert_class_t cls,
                                  alert_enable_t enabled) {
  if (index >= ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_MULTIREG_COUNT) {
    return kErrorAlertBadIndex;
  }
  index *= 4;

  switch (cls) {
    case kAlertClassA:
      abs_mmio_write32_shadowed(
          kBase + ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_REG_OFFSET + index,
          ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_CLASS_LA_0_VALUE_CLASSA);
      break;
    case kAlertClassB:
      abs_mmio_write32_shadowed(
          kBase + ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_REG_OFFSET + index,
          ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_CLASS_LA_0_VALUE_CLASSB);
      break;
    case kAlertClassC:
      abs_mmio_write32_shadowed(
          kBase + ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_REG_OFFSET + index,
          ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_CLASS_LA_0_VALUE_CLASSC);
      break;
    case kAlertClassD:
      abs_mmio_write32_shadowed(
          kBase + ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_REG_OFFSET + index,
          ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_CLASS_LA_0_VALUE_CLASSD);
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
      abs_mmio_write32_shadowed(
          kBase + ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_0_REG_OFFSET + index, 1);
      abs_mmio_write32(
          kBase + ALERT_HANDLER_LOC_ALERT_REGWEN_0_REG_OFFSET + index, 0);
      break;
    case kAlertEnableEnabled:
      abs_mmio_write32_shadowed(
          kBase + ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_0_REG_OFFSET + index, 1);
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
  reg = bitfield_field32_write(
      reg, ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E0_FIELD, 0);
  reg = bitfield_field32_write(
      reg, ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E1_FIELD, 1);
  reg = bitfield_field32_write(
      reg, ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E2_FIELD, 2);
  reg = bitfield_field32_write(
      reg, ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E3_FIELD, 3);

  // All of the alert class register blocks are identical but at different
  // offsets.  We'll treat everything like Class A, but add in the offset
  // to the other classes.
  switch (cls) {
    case kAlertClassA:
      offset = ALERT_HANDLER_CLASSA_CTRL_SHADOWED_REG_OFFSET -
               ALERT_HANDLER_CLASSA_CTRL_SHADOWED_REG_OFFSET;
      break;
    case kAlertClassB:
      offset = ALERT_HANDLER_CLASSB_CTRL_SHADOWED_REG_OFFSET -
               ALERT_HANDLER_CLASSA_CTRL_SHADOWED_REG_OFFSET;
      break;
    case kAlertClassC:
      offset = ALERT_HANDLER_CLASSC_CTRL_SHADOWED_REG_OFFSET -
               ALERT_HANDLER_CLASSA_CTRL_SHADOWED_REG_OFFSET;
      break;
    case kAlertClassD:
      offset = ALERT_HANDLER_CLASSD_CTRL_SHADOWED_REG_OFFSET -
               ALERT_HANDLER_CLASSA_CTRL_SHADOWED_REG_OFFSET;
      break;
    case kAlertClassX:
    default:
      return kErrorAlertBadClass;
  }
  switch (config->enabled) {
    case kAlertEnableLocked:
      reg = bitfield_bit32_write(
          reg, ALERT_HANDLER_CLASSA_CTRL_SHADOWED_LOCK_BIT, true);
      OT_FALLTHROUGH_INTENDED;
    case kAlertEnableEnabled:
      reg = bitfield_bit32_write(reg, ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_BIT,
                                 true);
      OT_FALLTHROUGH_INTENDED;
    case kAlertEnableNone:
      break;
    default:
      return kErrorAlertBadEnable;
  }
  switch (config->escalation) {
    case kAlertEscalatePhase3:
      reg = bitfield_bit32_write(
          reg, ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E3_BIT, true);
      OT_FALLTHROUGH_INTENDED;
    case kAlertEscalatePhase2:
      reg = bitfield_bit32_write(
          reg, ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E2_BIT, true);
      OT_FALLTHROUGH_INTENDED;
    case kAlertEscalatePhase1:
      reg = bitfield_bit32_write(
          reg, ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E1_BIT, true);
      OT_FALLTHROUGH_INTENDED;
    case kAlertEscalatePhase0:
      reg = bitfield_bit32_write(
          reg, ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E0_BIT, true);
      OT_FALLTHROUGH_INTENDED;
    case kAlertEscalateNone:
      break;
    default:
      return kErrorAlertBadEscalation;
  }

  abs_mmio_write32_shadowed(
      kBase + ALERT_HANDLER_CLASSA_CTRL_SHADOWED_REG_OFFSET + offset, reg);
  abs_mmio_write32_shadowed(
      kBase + ALERT_HANDLER_CLASSA_ACCUM_THRESH_SHADOWED_REG_OFFSET + offset,
      config->accum_threshold);
  abs_mmio_write32_shadowed(
      kBase + ALERT_HANDLER_CLASSA_TIMEOUT_CYC_SHADOWED_REG_OFFSET + offset,
      config->timeout_cycles);
  for (size_t i = 0; i < 4; ++i) {
    abs_mmio_write32_shadowed(
        kBase + ALERT_HANDLER_CLASSA_PHASE0_CYC_SHADOWED_REG_OFFSET + offset +
            i * 4,
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
  abs_mmio_write32_shadowed(
      kBase + ALERT_HANDLER_PING_TIMER_EN_SHADOWED_REG_OFFSET, 1);
  abs_mmio_write32(kBase + ALERT_HANDLER_PING_TIMER_REGWEN_REG_OFFSET, 0);
  return kErrorOk;
}

/**
 * Adds an alert handler register to a CRC32.
 *
 * @param[in, out] ctx Context variable.
 * @param offset Register offset relative to `kBase`.
 */
static void crc32_add_reg(uint32_t *ctx, uint32_t offset) {
  crc32_add32(ctx, abs_mmio_read32(kBase + offset));
}

/**
 * Adds a range of alert handler registers to a CRC32.
 *
 * @param[in, out] ctx Context variable.
 * @param offset Register offset relative to `kBase`.
 * @param num_regs Number of registers.
 */
static void crc32_add_regs(uint32_t *ctx, uint32_t offset, size_t num_regs) {
  for (size_t i = 0; i < num_regs; ++i, offset += sizeof(uint32_t)) {
    crc32_add_reg(ctx, offset);
  }
}

uint32_t alert_config_crc32(void) {
  uint32_t ctx;
  crc32_init(&ctx);

  crc32_add_regs(&ctx, ALERT_HANDLER_ALERT_REGWEN_0_REG_OFFSET,
                 ALERT_HANDLER_ALERT_REGWEN_MULTIREG_COUNT);
  crc32_add_regs(&ctx, ALERT_HANDLER_ALERT_EN_SHADOWED_0_REG_OFFSET,
                 ALERT_HANDLER_ALERT_EN_SHADOWED_MULTIREG_COUNT);
  crc32_add_regs(&ctx, ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_REG_OFFSET,
                 ALERT_HANDLER_ALERT_CLASS_SHADOWED_MULTIREG_COUNT);
  crc32_add_regs(&ctx, ALERT_HANDLER_LOC_ALERT_REGWEN_0_REG_OFFSET,
                 ALERT_HANDLER_LOC_ALERT_REGWEN_MULTIREG_COUNT);
  crc32_add_regs(&ctx, ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_0_REG_OFFSET,
                 ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_MULTIREG_COUNT);
  crc32_add_regs(&ctx, ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_REG_OFFSET,
                 ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_MULTIREG_COUNT);

  for (size_t class = 0; class < ALERT_HANDLER_PARAM_N_CLASSES; ++class) {
    enum {
      kClassStep = ALERT_HANDLER_CLASSB_REGWEN_REG_OFFSET -
                   ALERT_HANDLER_CLASSA_REGWEN_REG_OFFSET,
    };
    uint32_t classOffset = kClassStep * class;

    crc32_add_reg(&ctx, classOffset + ALERT_HANDLER_CLASSA_REGWEN_REG_OFFSET);
    crc32_add_reg(&ctx,
                  classOffset + ALERT_HANDLER_CLASSA_CTRL_SHADOWED_REG_OFFSET);
    crc32_add_reg(
        &ctx,
        classOffset + ALERT_HANDLER_CLASSA_ACCUM_THRESH_SHADOWED_REG_OFFSET);
    crc32_add_reg(
        &ctx,
        classOffset + ALERT_HANDLER_CLASSA_TIMEOUT_CYC_SHADOWED_REG_OFFSET);

    crc32_add_regs(
        &ctx, classOffset + ALERT_HANDLER_CLASSA_PHASE0_CYC_SHADOWED_REG_OFFSET,
        ALERT_HANDLER_PARAM_N_PHASES);
  }

  return crc32_finish(&ctx);
}

rom_error_t alert_config_check(lifecycle_state_t lc_state) {
  uint32_t crc32 = alert_config_crc32();
  rom_error_t res = lc_state ^ crc32;
  switch (launder32(lc_state)) {
    case kLcStateTest:
      HARDENED_CHECK_EQ(lc_state, kLcStateTest);
      enum {
        kMask = kLcStateTest ^ kErrorOk,
      };
      res ^= crc32 ^ kMask;
      break;
    case kLcStateProd:
      HARDENED_CHECK_EQ(lc_state, kLcStateProd);
      res ^=
          otp_read32(OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_ALERT_DIGEST_PROD_OFFSET);
      break;
    case kLcStateProdEnd:
      HARDENED_CHECK_EQ(lc_state, kLcStateProdEnd);
      res ^= otp_read32(
          OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_ALERT_DIGEST_PROD_END_OFFSET);
      break;
    case kLcStateDev:
      HARDENED_CHECK_EQ(lc_state, kLcStateDev);
      res ^=
          otp_read32(OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_ALERT_DIGEST_DEV_OFFSET);
      break;
    case kLcStateRma:
      HARDENED_CHECK_EQ(lc_state, kLcStateRma);
      res ^=
          otp_read32(OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_ALERT_DIGEST_RMA_OFFSET);
      break;
    default:
      HARDENED_TRAP();
  }
  if (launder32(res) != kErrorOk) {
    return kErrorAlertBadCrc32;
  }
  HARDENED_CHECK_EQ(res, kErrorOk);
  return res;
}
