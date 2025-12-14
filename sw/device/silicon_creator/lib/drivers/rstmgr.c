// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"

#include <assert.h>

#include "hw/top/dt/api.h"
#include "hw/top/dt/rstmgr.h"
#include "rstmgr.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"

#ifdef OT_PLATFORM_RV32
#include "sw/device/lib/runtime/hart.h"
#endif

#include "hw/top/otp_ctrl_regs.h"
#include "hw/top/rstmgr_regs.h"

static inline uint32_t rstmgr_base(void) {
  return dt_rstmgr_primary_reg_block(kDtRstmgrFirst);
}

void rstmgr_alert_info_collect(rstmgr_info_t *info) {
  info->length = bitfield_field32_read(
      abs_mmio_read32(rstmgr_base() + RSTMGR_ALERT_INFO_ATTR_REG_OFFSET),
      RSTMGR_ALERT_INFO_ATTR_CNT_AVAIL_FIELD);
  for (uint32_t i = 0; i < info->length; ++i) {
    abs_mmio_write32(
        rstmgr_base() + RSTMGR_ALERT_INFO_CTRL_REG_OFFSET,
        bitfield_field32_write(0, RSTMGR_ALERT_INFO_CTRL_INDEX_FIELD, i));
    info->info[i] =
        abs_mmio_read32(rstmgr_base() + RSTMGR_ALERT_INFO_REG_OFFSET);
  }
}

void rstmgr_cpu_info_collect(rstmgr_info_t *info) {
  info->length = bitfield_field32_read(
      abs_mmio_read32(rstmgr_base() + RSTMGR_CPU_INFO_ATTR_REG_OFFSET),
      RSTMGR_CPU_INFO_ATTR_CNT_AVAIL_FIELD);
  for (uint32_t i = 0; i < info->length; ++i) {
    abs_mmio_write32(
        rstmgr_base() + RSTMGR_CPU_INFO_CTRL_REG_OFFSET,
        bitfield_field32_write(0, RSTMGR_CPU_INFO_CTRL_INDEX_FIELD, i));
    info->info[i] = abs_mmio_read32(rstmgr_base() + RSTMGR_CPU_INFO_REG_OFFSET);
  }
}

uint32_t rstmgr_reason_get(void) {
  // Static assertions for bitfield indices.
#define REASON_ASSERT(index, expect) \
  static_assert((index) == (expect), #index " value incorrect.");

  REASON_ASSERT(kRstmgrReasonPowerOn, RSTMGR_RESET_INFO_POR_BIT);
  REASON_ASSERT(kRstmgrReasonLowPowerExit,
                RSTMGR_RESET_INFO_LOW_POWER_EXIT_BIT);
  REASON_ASSERT(kRstmgrReasonHardwareRequest, RSTMGR_RESET_INFO_HW_REQ_OFFSET);

#undef REASON_ASSERT

  return abs_mmio_read32(rstmgr_base() + RSTMGR_RESET_INFO_REG_OFFSET);
}

void rstmgr_reason_clear(uint32_t reasons) {
  abs_mmio_write32(rstmgr_base() + RSTMGR_RESET_INFO_REG_OFFSET, reasons);
}

void rstmgr_alert_info_enable(void) {
  abs_mmio_write32(rstmgr_base() + RSTMGR_ALERT_INFO_CTRL_REG_OFFSET, 1);
}

void rstmgr_cpu_info_enable(void) {
  abs_mmio_write32(rstmgr_base() + RSTMGR_CPU_INFO_CTRL_REG_OFFSET, 1);
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
          abs_mmio_read32(rstmgr_base() + RSTMGR_ALERT_INFO_CTRL_REG_OFFSET),
          RSTMGR_ALERT_INFO_CTRL_EN_BIT)) {
    alert_info ^= launder32(kByteTrueXorFalse);
  }
  uint32_t cpu_info = launder32(kHardenedByteBoolFalse);
  if (bitfield_bit32_read(
          abs_mmio_read32(rstmgr_base() + RSTMGR_CPU_INFO_CTRL_REG_OFFSET),
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
  abs_mmio_write32(rstmgr_base() + RSTMGR_RESET_REQ_REG_OFFSET,
                   kMultiBitBool4True);
#ifdef OT_PLATFORM_RV32
  // Wait until the chip resets.
  while (true) {
    wait_for_interrupt();
  }
#endif
}

bool rstmgr_is_hw_reset_reason(dt_rstmgr_t dt, uint32_t reasons,
                               dt_instance_id_t inst_id, size_t reset_req) {
  for (size_t idx = 0; idx < dt_rstmgr_hw_reset_req_src_count(dt); idx++) {
    if (!(reasons & (1 << (idx + RSTMGR_RESET_INFO_HW_REQ_OFFSET)))) {
      continue;
    }

    dt_rstmgr_reset_req_src_t hw_reset_req =
        dt_rstmgr_hw_reset_req_src(dt, idx);
    if (hw_reset_req.inst_id == kDtInstanceIdUnknown) {
      continue;
    }

    if ((hw_reset_req.inst_id == inst_id) &&
        (hw_reset_req.reset_req == reset_req)) {
      return true;
    }
  }

  return false;
}
