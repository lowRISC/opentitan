// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/otp.h"

#include <stddef.h>

#include "sw/device/lib/base/bitfield.h"
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

static void wait_for_dai_idle(void) {
  uint32_t status = 0;
  bool idle = false;
  do {
    status = sec_mmio_read32(kBase + OTP_CTRL_STATUS_REG_OFFSET);
    idle = bitfield_bit32_read(status, OTP_CTRL_STATUS_DAI_IDLE_BIT);
  } while (!idle);
}

static void dai_read_blocking(uint32_t address) {
  wait_for_dai_idle();
  sec_mmio_write32(kBase + OTP_CTRL_DIRECT_ACCESS_ADDRESS_REG_OFFSET, address);
  uint32_t cmd =
      bitfield_bit32_write(0, OTP_CTRL_DIRECT_ACCESS_CMD_RD_BIT, true);
  sec_mmio_write32(kBase + OTP_CTRL_DIRECT_ACCESS_CMD_REG_OFFSET, cmd);
  wait_for_dai_idle();
}

uint32_t otp_dai_read32(uint32_t address) {
  SEC_MMIO_ASSERT_WRITE_INCREMENT(kOtpSecMmioDaiRead32, 2);
  dai_read_blocking(address);
  return sec_mmio_read32(kBase + OTP_CTRL_DIRECT_ACCESS_RDATA_0_REG_OFFSET);
}

uint64_t otp_dai_read64(uint32_t address) {
  SEC_MMIO_ASSERT_WRITE_INCREMENT(kOtpSecMmioDaiRead64, 2);
  dai_read_blocking(address);
  uint64_t value =
      sec_mmio_read32(kBase + OTP_CTRL_DIRECT_ACCESS_RDATA_1_REG_OFFSET);
  value <<= 32;
  value |= sec_mmio_read32(kBase + OTP_CTRL_DIRECT_ACCESS_RDATA_0_REG_OFFSET);
  return value;
}

void otp_creator_sw_cfg_lockdown(void) {
  SEC_MMIO_ASSERT_WRITE_INCREMENT(kOtpSecMmioCreatorSwCfgLockDown, 1);
  sec_mmio_write32(kBase + OTP_CTRL_CREATOR_SW_CFG_READ_LOCK_REG_OFFSET, 0);
}
