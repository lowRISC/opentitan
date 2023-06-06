// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"

#include <assert.h>

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"

#ifdef OT_PLATFORM_RV32
#include "sw/device/lib/runtime/hart.h"
#endif

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"
#include "rstmgr_regs.h"

enum {
  kBase = TOP_EARLGREY_RSTMGR_AON_BASE_ADDR,
};

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
  // Static assertions for bitfield indices.
#define REASON_ASSERT(index, expect) \
  static_assert((index) == (expect), #index " value incorrect.");

  REASON_ASSERT(kRstmgrReasonPowerOn, RSTMGR_RESET_INFO_POR_BIT);
  REASON_ASSERT(kRstmgrReasonLowPowerExit,
                RSTMGR_RESET_INFO_LOW_POWER_EXIT_BIT);
  REASON_ASSERT(kRstmgrReasonSysrstCtrl,
                RSTMGR_RESET_INFO_HW_REQ_OFFSET +
                    kTopEarlgreyPowerManagerResetRequestsSysrstCtrlAonRstReq);
  REASON_ASSERT(
      kRstmgrReasonWatchdog,
      RSTMGR_RESET_INFO_HW_REQ_OFFSET +
          kTopEarlgreyPowerManagerResetRequestsAonTimerAonAonTimerRstReq);

  // Alert escalation is one bit after the reset request index for the last
  // peripheral.
  REASON_ASSERT(kRstmgrReasonEscalation,
                RSTMGR_RESET_INFO_HW_REQ_OFFSET +
                    kTopEarlgreyPowerManagerResetRequestsLast + 2)

  // Check that the last index corresponds to the last bit in HW_REQ.
  static_assert(
      ((1 << (kRstmgrReasonLast - RSTMGR_RESET_INFO_HW_REQ_OFFSET + 1)) - 1) ==
          RSTMGR_RESET_INFO_HW_REQ_MASK,
      "kRstmgrReasonLast value incorrect.");

#undef REASON_ASSERT

  return abs_mmio_read32(kBase + RSTMGR_RESET_INFO_REG_OFFSET);
}

void rstmgr_reason_clear(uint32_t reasons) {
  abs_mmio_write32(kBase + RSTMGR_RESET_INFO_REG_OFFSET, reasons);
}

void rstmgr_alert_info_enable(void) {
  abs_mmio_write32(kBase + RSTMGR_ALERT_INFO_CTRL_REG_OFFSET, 1);
}

rom_error_t rstmgr_info_en_check(uint32_t reset_reasons) {
  enum {
    kByteTrueXorFalse = kHardenedByteBoolTrue ^ kHardenedByteBoolFalse,
    kOkXorError = kErrorOk ^ kErrorRstmgrBadInit,
  };
  // Read the OTP item. Set OTP item's fields that are not enabled to
  // `kHardenedByteFalse`.
  uint32_t otp =
      otp_read32(OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_RSTMGR_INFO_EN_OFFSET);
  if (bitfield_field32_read(otp, RSTMGR_OTP_FIELD_ALERT_INFO_EN) !=
      kHardenedByteBoolTrue) {
    otp = bitfield_field32_write(otp, RSTMGR_OTP_FIELD_ALERT_INFO_EN,
                                 kHardenedByteBoolFalse);
  }
  if (bitfield_field32_read(otp, RSTMGR_OTP_FIELD_CPU_INFO_EN) !=
      kHardenedByteBoolTrue) {
    otp = bitfield_field32_write(otp, RSTMGR_OTP_FIELD_CPU_INFO_EN,
                                 kHardenedByteBoolFalse);
  }
  barrier32(otp);
  // Prepare the expected OTP value from rstmgr.
  uint32_t alert_info = launder32(kHardenedByteBoolFalse);
  if (bitfield_bit32_read(
          abs_mmio_read32(kBase + RSTMGR_ALERT_INFO_CTRL_REG_OFFSET),
          RSTMGR_ALERT_INFO_CTRL_EN_BIT)) {
    alert_info ^= launder32(kByteTrueXorFalse);
  }
  uint32_t cpu_info = launder32(kHardenedByteBoolFalse);
  if (bitfield_bit32_read(
          abs_mmio_read32(kBase + RSTMGR_CPU_INFO_CTRL_REG_OFFSET),
          RSTMGR_CPU_INFO_CTRL_EN_BIT)) {
    cpu_info ^= launder32(kByteTrueXorFalse);
  }
  // Compare.
  uint32_t expected =
      bitfield_field32_write(0, RSTMGR_OTP_FIELD_ALERT_INFO_EN, alert_info);
  expected =
      bitfield_field32_write(expected, RSTMGR_OTP_FIELD_CPU_INFO_EN, cpu_info);
  expected ^= launder32(kOkXorError);
  barrier32(expected);
  uint32_t res = launder32(kErrorRstmgrBadInit);
  bool low_power_exit =
      bitfield_bit32_read(reset_reasons, kRstmgrReasonLowPowerExit);
  if (launder32(low_power_exit)) {
    HARDENED_CHECK_EQ(low_power_exit, 1);
    res ^= kOkXorError;
  } else {
    HARDENED_CHECK_EQ(low_power_exit, 0);
    res ^= otp ^ expected;
  }
  if (launder32(res) == kErrorOk) {
    HARDENED_CHECK_EQ(res, kErrorOk);
    return res;
  }
  return kErrorRstmgrBadInit;
}

void rstmgr_reset(void) {
  abs_mmio_write32(kBase + RSTMGR_RESET_REQ_REG_OFFSET, kMultiBitBool4True);
#ifdef OT_PLATFORM_RV32
  // Wait until the chip resets.
  while (true) {
    wait_for_interrupt();
  }
#endif
}
