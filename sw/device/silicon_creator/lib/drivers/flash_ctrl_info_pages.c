// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"

#include "flash_ctrl_regs.h"

#define INFO_PAGE_STRUCT_(name_, bank_, page_)                                 \
  const flash_ctrl_info_page_t name_ = {                                       \
      .base_addr = (bank_)*FLASH_CTRL_PARAM_BYTES_PER_BANK +                   \
                   (page_)*FLASH_CTRL_PARAM_BYTES_PER_PAGE,                    \
      .cfg_wen_off =                                                           \
          FLASH_CTRL_BANK##bank_##_INFO0_REGWEN_##page_##_REG_OFFSET,          \
      .cfg_off = FLASH_CTRL_BANK##bank_##_INFO0_PAGE_CFG_##page_##_REG_OFFSET, \
  };

FLASH_CTRL_INFO_PAGES_DEFINE(INFO_PAGE_STRUCT_)
#undef INFO_PAGE_STRUCT_
