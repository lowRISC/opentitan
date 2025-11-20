// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/otp.h"

#include <stddef.h>

#include "hw/top/dt/dt_otp_ctrl.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "hw/top/otp_ctrl_regs.h"  // Generated.

static inline uint32_t otp_ctrl_base(void) {
  return dt_otp_ctrl_primary_reg_block(kDtOtpCtrl);
}

uint32_t otp_read32(uint32_t address) {
  return sec_mmio_read32(otp_ctrl_base() + OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET +
                         address);
}

uint64_t otp_read64(uint32_t address) {
  uint32_t reg_offset = OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET + address;
  uint64_t value =
      sec_mmio_read32(otp_ctrl_base() + reg_offset + sizeof(uint32_t));
  value <<= 32;
  value |= sec_mmio_read32(otp_ctrl_base() + reg_offset);

  return value;
}

void otp_read(uint32_t address, uint32_t *data, size_t num_words) {
  uint32_t reg_offset = OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET + address;
  size_t i = 0, r = num_words - 1;
  for (; launder32(i) < num_words && launder32(r) < num_words; ++i, --r) {
    data[i] =
        sec_mmio_read32(otp_ctrl_base() + reg_offset + i * sizeof(uint32_t));
  }
  HARDENED_CHECK_EQ(i, num_words);
  HARDENED_CHECK_EQ(r, SIZE_MAX);
}

dt_otp_partition_info_t otp_readable_partition_info(otp_partition_t partition) {
  HARDENED_CHECK_LT(partition, kOtpPartitionCount);
  dt_otp_partition_info_t partition_info =
      dt_otp_ctrl_sw_readable_partition(kDtOtpCtrl, partition);
  HARDENED_CHECK_GT(partition_info.size, 0);

  return partition_info;
}

uint64_t otp_partition_digest_read(otp_partition_t partition) {
  uint32_t reg_offset =
      otp_ctrl_base() +
      otp_readable_partition_info(partition).digest_reg_offset;
  uint64_t value = sec_mmio_read32(reg_offset + sizeof(uint32_t));
  value <<= 32;
  value |= sec_mmio_read32(reg_offset);
  return value;
}

static void wait_for_dai_idle(void) {
  uint32_t status = 0;
  bool idle = false;
  do {
    status = abs_mmio_read32(otp_ctrl_base() + OTP_CTRL_STATUS_REG_OFFSET);
    idle = bitfield_bit32_read(status, OTP_CTRL_STATUS_DAI_IDLE_BIT);
  } while (!idle);
}

static void dai_read_blocking(otp_partition_t partition,
                              uint32_t relative_address) {
  wait_for_dai_idle();
  HARDENED_CHECK_EQ(
      relative_address & otp_readable_partition_info(partition).align_mask, 0);
  abs_mmio_write32(
      otp_ctrl_base() + OTP_CTRL_DIRECT_ACCESS_ADDRESS_REG_OFFSET,
      otp_readable_partition_info(partition).start_addr + relative_address);
  uint32_t cmd =
      bitfield_bit32_write(0, OTP_CTRL_DIRECT_ACCESS_CMD_RD_BIT, true);
  abs_mmio_write32(otp_ctrl_base() + OTP_CTRL_DIRECT_ACCESS_CMD_REG_OFFSET,
                   cmd);
  wait_for_dai_idle();
}

uint32_t otp_dai_read32(otp_partition_t partition, uint32_t relative_address) {
  dai_read_blocking(partition, relative_address);
  return abs_mmio_read32(otp_ctrl_base() +
                         OTP_CTRL_DIRECT_ACCESS_RDATA_0_REG_OFFSET);
}

uint64_t otp_dai_read64(otp_partition_t partition, uint32_t relative_address) {
  dai_read_blocking(partition, relative_address);
  uint64_t value = abs_mmio_read32(otp_ctrl_base() +
                                   OTP_CTRL_DIRECT_ACCESS_RDATA_1_REG_OFFSET);
  value <<= 32;
  value |= abs_mmio_read32(otp_ctrl_base() +
                           OTP_CTRL_DIRECT_ACCESS_RDATA_0_REG_OFFSET);
  return value;
}

rom_error_t otp_dai_read(otp_partition_t partition, uint32_t relative_address,
                         uint32_t *data, size_t num_words) {
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
  sec_mmio_write32(
      otp_ctrl_base() + OTP_CTRL_CREATOR_SW_CFG_READ_LOCK_REG_OFFSET, 0);
}
