// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/status.h"
#include "sw/ip/lc_ctrl/dif/dif_lc_ctrl.h"
#include "sw/ip/lc_ctrl/test/utils/lc_ctrl_testutils.h"
#include "sw/lib/sw/device/base/csr.h"
#include "sw/lib/sw/device/runtime/log.h"
#include "sw/lib/sw/device/silicon_creator/epmp_defs.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  static_assert(EXPECT_DEBUG == 0 || EXPECT_DEBUG == 1,
                "EXPECT_DEBUG must be `0` or `1`.");

  dif_lc_ctrl_t lc_ctrl;
  mmio_region_t lc_reg =
      mmio_region_from_addr(TOP_DARJEELING_LC_CTRL_REGS_BASE_ADDR);
  CHECK_DIF_OK(dif_lc_ctrl_init(lc_reg, &lc_ctrl));
  bool debug_enabled = false;
  CHECK_STATUS_OK(
      lc_ctrl_testutils_debug_func_enabled(&lc_ctrl, &debug_enabled));
  LOG_INFO("debug_enabled: %d", debug_enabled);

  if (debug_enabled != EXPECT_DEBUG) {
    LOG_ERROR("Expected debug_enabled=%d", EXPECT_DEBUG);
    return false;
  }

  uint32_t pmpaddr13;
  CSR_READ(CSR_REG_PMPADDR13, &pmpaddr13);
  uint32_t pmpcfg3;
  CSR_READ(CSR_REG_PMPCFG3, &pmpcfg3);
  uint8_t pmp13cfg = (pmpcfg3 >> 8) & 0xff;
  LOG_INFO("pmpaddr13=0x%08x, pmpcfg3=0x%08x, pmp13cfg=0x%02x", pmpaddr13,
           pmpcfg3, pmp13cfg);

  const uint32_t kPmpEncodedDebugRomRange =
      (TOP_DARJEELING_RV_DM_MEM_BASE_ADDR >> 2) |
      ((TOP_DARJEELING_RV_DM_MEM_SIZE_BYTES - 1) >> 3);
  if (pmpaddr13 != kPmpEncodedDebugRomRange) {
    LOG_ERROR("Expected pmpaddr13=0x%08x", kPmpEncodedDebugRomRange);
    return false;
  }

  const uint8_t kExpectedPmp13cfg =
      debug_enabled
          ? EPMP_CFG_L | EPMP_CFG_A_NAPOT | EPMP_CFG_X | EPMP_CFG_W | EPMP_CFG_R
          : EPMP_CFG_L | EPMP_CFG_A_NAPOT;
  if (pmp13cfg != kExpectedPmp13cfg) {
    LOG_ERROR("Expected pmp13cfg=0x%02x", kExpectedPmp13cfg);
    return false;
  }

  return true;
}
