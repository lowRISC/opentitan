// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/boot_log.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"

#include "flash_ctrl_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

status_t flash_contents_print(boot_log_t *boot_log) {
  TRY(boot_log_check(boot_log));
  uint32_t *data = (uint32_t *)(TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR +
                                boot_log->rom_ext_size);
  uint32_t *end = (uint32_t *)(TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR +
                               FLASH_CTRL_PARAM_BYTES_PER_BANK);
  uint32_t incr = FLASH_CTRL_PARAM_BYTES_PER_PAGE / sizeof(uint32_t);

  for (; data < end; data += incr) {
    LOG_INFO("flash %p = %x", data, *data);
  }
  return OK_STATUS();
}

bool test_main(void) {
  status_t sts = flash_contents_print(&retention_sram_get()->creator.boot_log);
  if (status_err(sts)) {
    LOG_ERROR("flash_contents_print: %r", sts);
  }
  return status_ok(sts);
}
