// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"

#include "flash_ctrl_regs.h"

#ifdef OT_IS_ENGLISH_BREAKFAST
#include "hw/top_englishbreakfast/sw/autogen/top_englishbreakfast.h"
#else
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#endif

enum {
/**
 * Base address of the flash_ctrl registers.
 */
#ifdef OT_IS_ENGLISH_BREAKFAST
  kBase = TOP_ENGLISHBREAKFAST_FLASH_CTRL_CORE_BASE_ADDR,
#else
  kBase = TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR,
#endif
};

#define INFO_PAGE_STRUCT_(name_, bank_, page_)                                \
  const flash_ctrl_info_page_t name_ = {                                      \
      .base_addr = (bank_)*FLASH_CTRL_PARAM_BYTES_PER_BANK +                  \
                   (page_)*FLASH_CTRL_PARAM_BYTES_PER_PAGE,                   \
      .cfg_wen_addr =                                                         \
          kBase + FLASH_CTRL_BANK##bank_##_INFO0_REGWEN_##page_##_REG_OFFSET, \
      .cfg_addr =                                                             \
          kBase +                                                             \
          FLASH_CTRL_BANK##bank_##_INFO0_PAGE_CFG_##page_##_REG_OFFSET,       \
  };

FLASH_CTRL_INFO_PAGES_DEFINE(INFO_PAGE_STRUCT_)
#undef INFO_PAGE_STRUCT_
