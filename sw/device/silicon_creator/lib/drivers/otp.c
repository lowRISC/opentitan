// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/otp.h"

#include <stddef.h>

#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"  // Generated.

enum { kBase = TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR };

uint32_t otp_read32(uint32_t address) {
  return sec_mmio_read32(kBase + OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET + address);
}

uint64_t otp_read64(uint32_t address) {
  uint32_t reg_offset = OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET + address;
  uint64_t value = sec_mmio_read32(kBase + reg_offset + sizeof(uint32_t));
  value <<= 32;
  value |= sec_mmio_read32(kBase + reg_offset);

  return value;
}

void otp_read(uint32_t address, uint32_t *data, size_t num_words) {
  uint32_t reg_offset = OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET + address;
  size_t i = 0, r = num_words - 1;
  for (; launder32(i) < num_words && launder32(r) < num_words; ++i, --r) {
    data[i] = sec_mmio_read32(kBase + reg_offset + i * sizeof(uint32_t));
  }
  HARDENED_CHECK_EQ(i, num_words);
  HARDENED_CHECK_EQ((uint32_t)r, UINT32_MAX);
}

void otp_creator_sw_cfg_lockdown(void) {
  SEC_MMIO_ASSERT_WRITE_INCREMENT(kOtpSecMmioCreatorSwCfgLockDown, 1);
  sec_mmio_write32(kBase + OTP_CTRL_CREATOR_SW_CFG_READ_LOCK_REG_OFFSET, 0);
}
