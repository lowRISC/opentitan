// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

enum {
  kFlashCtrlPrimCsr0RegwenRegOffset = 0x0,
  kFlashCtrlPrimCsr1RegOffset = 0x4,
};

static status_t test_flash_ctrl_prim_lockdown(void) {
  uint32_t regwen = abs_mmio_read32(TOP_EARLGREY_FLASH_CTRL_PRIM_BASE_ADDR +
                                    kFlashCtrlPrimCsr0RegwenRegOffset);
  LOG_INFO("flash_ctrl_prim csr0_regwen = %x", regwen);
  TRY_CHECK(regwen == 0, "CSR0_REGWEN expected 0, got %x", regwen);

  // Attempt to write 1 to CSR0_REGWEN (RW0C: should remain 0).
  abs_mmio_write32(TOP_EARLGREY_FLASH_CTRL_PRIM_BASE_ADDR +
                       kFlashCtrlPrimCsr0RegwenRegOffset,
                   1);
  regwen = abs_mmio_read32(TOP_EARLGREY_FLASH_CTRL_PRIM_BASE_ADDR +
                           kFlashCtrlPrimCsr0RegwenRegOffset);
  TRY_CHECK(regwen == 0, "CSR0_REGWEN should remain 0 after write 1, got %x",
            regwen);

  // Attempt to write to CSR1 (protected by CSR0_REGWEN).
  uint32_t csr1_before = abs_mmio_read32(
      TOP_EARLGREY_FLASH_CTRL_PRIM_BASE_ADDR + kFlashCtrlPrimCsr1RegOffset);
  abs_mmio_write32(
      TOP_EARLGREY_FLASH_CTRL_PRIM_BASE_ADDR + kFlashCtrlPrimCsr1RegOffset,
      0x1fff);
  uint32_t csr1_after = abs_mmio_read32(TOP_EARLGREY_FLASH_CTRL_PRIM_BASE_ADDR +
                                        kFlashCtrlPrimCsr1RegOffset);
  TRY_CHECK(csr1_after == csr1_before,
            "CSR1 modified despite CSR0_REGWEN lock: before=%x, after=%x",
            csr1_before, csr1_after);

  return OK_STATUS();
}

bool test_main(void) {
  status_t sts = test_flash_ctrl_prim_lockdown();
  if (status_err(sts)) {
    LOG_ERROR("flash_ctrl_prim_lockdown: %r", sts);
  }
  return status_ok(sts);
}
