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

enum { kBase = TOP_EARLGREY_OTP_CTRL_BASE_ADDR };

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

rom_error_t otp_read(uint32_t address, void *data, size_t len) {
  // TODO Update to use alignment utility functions.
  // https://github.com/lowRISC/opentitan/issues/6112
  if (address % alignof(uint32_t) != 0 || len % sizeof(uint32_t) != 0) {
    return kErrorOtpBadAlignment;
  }

  uint32_t reg_offset = OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET + address;
  for (size_t i = 0; i < len; i += sizeof(uint32_t)) {
    uint32_t word = sec_mmio_read32(kBase + reg_offset + i);
    memcpy(data + i, &word, sizeof(uint32_t));
  }

  return kErrorOk;
}
