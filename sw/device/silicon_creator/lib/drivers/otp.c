// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/otp.h"

#include <stddef.h>

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"  // Generated.

enum {
  kBase = TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR,
};

// This is generates too many lines with different formatting variants, so
// We opt to just disable formatting.
// clang-format off
const otp_partition_info_t kOtpPartitions[] = {
    [kOtpPartitionCreatorSwCfg] = {
        .start_addr = OTP_CTRL_PARAM_CREATOR_SW_CFG_OFFSET,
        .size = OTP_CTRL_PARAM_CREATOR_SW_CFG_SIZE -
                OTP_CTRL_PARAM_CREATOR_SW_CFG_DIGEST_SIZE,
        .digest_addr = OTP_CTRL_CREATOR_SW_CFG_DIGEST_0_REG_OFFSET,
        .align_mask = 0x3},
    [kOtpPartitionOwnerSwCfg] = {
        .start_addr = OTP_CTRL_PARAM_OWNER_SW_CFG_OFFSET,
        .size = OTP_CTRL_PARAM_OWNER_SW_CFG_SIZE -
                OTP_CTRL_PARAM_OWNER_SW_CFG_DIGEST_SIZE,
        .digest_addr = OTP_CTRL_OWNER_SW_CFG_DIGEST_0_REG_OFFSET,
        .align_mask = 0x3},
    [kOtpPartitionRotCreatorAuthCodesign] = {
        .start_addr = OTP_CTRL_PARAM_ROT_CREATOR_AUTH_CODESIGN_OFFSET,
        .size = OTP_CTRL_PARAM_ROT_CREATOR_AUTH_CODESIGN_SIZE -
                OTP_CTRL_PARAM_ROT_CREATOR_AUTH_CODESIGN_DIGEST_SIZE,
        .digest_addr = OTP_CTRL_ROT_CREATOR_AUTH_CODESIGN_DIGEST_0_REG_OFFSET,
        .align_mask = 0x3},
    [kOtpPartitionRotCreatorAuthState] = {
        .start_addr = OTP_CTRL_PARAM_ROT_CREATOR_AUTH_STATE_OFFSET,
        .size = OTP_CTRL_PARAM_ROT_CREATOR_AUTH_STATE_SIZE -
                OTP_CTRL_PARAM_ROT_CREATOR_AUTH_STATE_DIGEST_SIZE,
        .digest_addr = OTP_CTRL_ROT_CREATOR_AUTH_STATE_DIGEST_0_REG_OFFSET,
        .align_mask = 0x3},
    [kOtpPartitionHwCfg0] = {
        .start_addr = OTP_CTRL_PARAM_HW_CFG0_OFFSET,
        .size = OTP_CTRL_PARAM_HW_CFG0_SIZE -
                OTP_CTRL_PARAM_HW_CFG0_DIGEST_SIZE,
        .digest_addr = OTP_CTRL_HW_CFG0_DIGEST_0_REG_OFFSET,
        .align_mask = 0x3},
    [kOtpPartitionHwCfg1] = {
        .start_addr = OTP_CTRL_PARAM_HW_CFG1_OFFSET,
        .size = OTP_CTRL_PARAM_HW_CFG1_SIZE -
                OTP_CTRL_PARAM_HW_CFG1_DIGEST_SIZE,
        .digest_addr = OTP_CTRL_HW_CFG1_DIGEST_0_REG_OFFSET,
        .align_mask = 0x3},
};
// clang-format on

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
  HARDENED_CHECK_EQ(r, SIZE_MAX);
}

uint64_t otp_partition_digest_read(otp_partition_t partition) {
  uint32_t reg_offset = kBase + kOtpPartitions[partition].digest_addr;
  uint64_t value = sec_mmio_read32(reg_offset + sizeof(uint32_t));
  value <<= 32;
  value |= sec_mmio_read32(reg_offset);
  return value;
}

static void wait_for_dai_idle(void) {
  uint32_t status = 0;
  bool idle = false;
  do {
    status = abs_mmio_read32(kBase + OTP_CTRL_STATUS_REG_OFFSET);
    idle = bitfield_bit32_read(status, OTP_CTRL_STATUS_DAI_IDLE_BIT);
  } while (!idle);
}

static void dai_read_blocking(otp_partition_t partition,
                              uint32_t relative_address) {
  wait_for_dai_idle();
  HARDENED_CHECK_EQ(relative_address & kOtpPartitions[partition].align_mask, 0);
  abs_mmio_write32(kBase + OTP_CTRL_DIRECT_ACCESS_ADDRESS_REG_OFFSET,
                   kOtpPartitions[partition].start_addr + relative_address);
  uint32_t cmd =
      bitfield_bit32_write(0, OTP_CTRL_DIRECT_ACCESS_CMD_RD_BIT, true);
  abs_mmio_write32(kBase + OTP_CTRL_DIRECT_ACCESS_CMD_REG_OFFSET, cmd);
  wait_for_dai_idle();
}

uint32_t otp_dai_read32(otp_partition_t partition, uint32_t relative_address) {
  dai_read_blocking(partition, relative_address);
  return abs_mmio_read32(kBase + OTP_CTRL_DIRECT_ACCESS_RDATA_0_REG_OFFSET);
}

uint64_t otp_dai_read64(otp_partition_t partition, uint32_t relative_address) {
  dai_read_blocking(partition, relative_address);
  uint64_t value =
      abs_mmio_read32(kBase + OTP_CTRL_DIRECT_ACCESS_RDATA_1_REG_OFFSET);
  value <<= 32;
  value |= abs_mmio_read32(kBase + OTP_CTRL_DIRECT_ACCESS_RDATA_0_REG_OFFSET);
  return value;
}

rom_error_t otp_dai_read(otp_partition_t partition, uint32_t relative_address,
                         uint32_t *data, size_t num_words) {
  HARDENED_CHECK_LT(partition, ARRAYSIZE(kOtpPartitions));
  size_t i = 0, r = num_words - 1;
  uint32_t addr = relative_address;
  for (; launder32(i) < num_words && launder32(r) < num_words; ++i, --r) {
    data[i] = otp_dai_read32(partition, addr);
    addr += sizeof(uint32_t);
  }
  HARDENED_CHECK_EQ(i, num_words);
  HARDENED_CHECK_EQ(r, SIZE_MAX);
  return kErrorOk;
}

void otp_creator_sw_cfg_lockdown(void) {
  SEC_MMIO_ASSERT_WRITE_INCREMENT(kOtpSecMmioCreatorSwCfgLockDown, 1);
  sec_mmio_write32(kBase + OTP_CTRL_CREATOR_SW_CFG_READ_LOCK_REG_OFFSET, 0);
}
