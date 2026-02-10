// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/dbg_print.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.
#include "sram_ctrl_regs.h"                           // Generated.

OTTF_DEFINE_TEST_CONFIG();

enum {
  kBase = TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR,
};

OT_NO_COVERAGE
int test_stub(void) { return 0x42; }

// SRAM copy of `test_stub` bytecodes.
uint32_t test_stub_sram[32];

bool test_main(void) {
  // Try to enable SRAM_EXEC
  uint32_t reg_before = abs_mmio_read32(kBase + SRAM_CTRL_EXEC_REG_OFFSET);
  uint32_t reg_wen = abs_mmio_read32(kBase + SRAM_CTRL_EXEC_REGWEN_REG_OFFSET);
  abs_mmio_write32(kBase + SRAM_CTRL_EXEC_REG_OFFSET, kMultiBitBool4True);
  uint32_t reg_after = abs_mmio_read32(kBase + SRAM_CTRL_EXEC_REG_OFFSET);
  dbg_printf("value = %x, %x, %x\r\n", reg_before, reg_after, reg_wen);

  // Try to execute code on SRAM.
  memcpy(test_stub_sram, test_stub, sizeof(test_stub_sram));
  int result = ((int (*)(void))test_stub_sram)();

  return result == 0x42;
}
