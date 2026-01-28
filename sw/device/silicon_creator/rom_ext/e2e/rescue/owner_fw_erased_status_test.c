// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/base/chip.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"

#include "flash_ctrl_regs.h"

enum {
  kOwnerSlotAOffset = CHIP_ROM_EXT_SIZE_MAX,
  kOwnerSlotBOffset = FLASH_CTRL_PARAM_BYTES_PER_BANK + CHIP_ROM_EXT_SIZE_MAX,
};

OTTF_DEFINE_TEST_CONFIG();

const char *is_erased(uint32_t addr) {
  if (flash_ctrl_data_erase_verify(addr, kFlashCtrlEraseTypePage) == kErrorOk) {
    return "ERASED";
  }
  return "PROGRAMMED";
}

bool test_main(void) {
  LOG_INFO("Owner slots status: %s / %s", is_erased(kOwnerSlotAOffset),
           is_erased(kOwnerSlotBOffset));

  // The test harness will not catch this log if both lines above are expected.
  return false;
}
