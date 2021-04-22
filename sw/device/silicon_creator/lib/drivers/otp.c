// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/otp.h"

#include <stddef.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "otp_ctrl_regs.h"

uint32_t otp_read32(const otp_t *otp, uint32_t address) {
  return mmio_region_read32(otp->base_addr,
                            OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET + address);
}

uint64_t otp_read64(const otp_t *otp, uint32_t address) {
  ptrdiff_t reg_offset = OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET + address;
  uint64_t value =
      mmio_region_read32(otp->base_addr, reg_offset + sizeof(uint32_t));
  value <<= 32;
  value |= mmio_region_read32(otp->base_addr, reg_offset);

  return value;
}

void otp_read(const otp_t *otp, uint32_t address, void *data, size_t len) {
  ptrdiff_t reg_offset = OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET + address;
  mmio_region_memcpy_from_mmio32(otp->base_addr, reg_offset, data, len);
}
