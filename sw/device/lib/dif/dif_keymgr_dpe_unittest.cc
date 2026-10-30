// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_keymgr_dpe.h"

#include <array>

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "hw/top/keymgr_dpe_regs.h"  // Generated

namespace dif_keymgr_dpe_unittest {
namespace {

// TODO(#30609): Write these unittests

class KeymgrDpeTest : public testing::Test, public mock_mmio::MmioTest {
 protected:
  dif_keymgr_dpe_t keymgr_dpe_ = {.base_addr = dev().region()};
};

class EraseSlotTest : public KeymgrDpeTest {};

TEST_F(EraseSlotTest, NullArgs) {
  dif_keymgr_dpe_erase_params_t params = {.slot_dst_sel = 1};
  EXPECT_DIF_BADARG(dif_keymgr_dpe_erase_slot(nullptr, &params));
  EXPECT_DIF_BADARG(dif_keymgr_dpe_erase_slot(&keymgr_dpe_, nullptr));
}

class GetStatusCodesTest : public KeymgrDpeTest {};

TEST_F(GetStatusCodesTest, Wip) {
  EXPECT_READ32(KEYMGR_DPE_OP_STATUS_REG_OFFSET,
                KEYMGR_DPE_OP_STATUS_STATUS_VALUE_WIP);

  dif_keymgr_dpe_status_codes_t status_codes;
  EXPECT_DIF_OK(dif_keymgr_dpe_get_status_codes(&keymgr_dpe_, &status_codes));
  EXPECT_EQ(status_codes, 0);
}

TEST_F(GetStatusCodesTest, Idle) {
  EXPECT_READ32(KEYMGR_DPE_OP_STATUS_REG_OFFSET,
                KEYMGR_DPE_OP_STATUS_STATUS_VALUE_IDLE);
  EXPECT_READ32(KEYMGR_DPE_ERR_CODE_REG_OFFSET, 0);
  EXPECT_WRITE32(KEYMGR_DPE_ERR_CODE_REG_OFFSET, 0);

  dif_keymgr_dpe_status_codes_t status_codes;
  EXPECT_DIF_OK(dif_keymgr_dpe_get_status_codes(&keymgr_dpe_, &status_codes));
  EXPECT_EQ(status_codes, kDifKeymgrDpeStatusCodeIdle);
}

TEST_F(GetStatusCodesTest, IdleWithShadowUpdateError) {
  // A shadow register update error is raised outside of any operation.
  EXPECT_READ32(KEYMGR_DPE_OP_STATUS_REG_OFFSET,
                KEYMGR_DPE_OP_STATUS_STATUS_VALUE_IDLE);
  EXPECT_READ32(KEYMGR_DPE_ERR_CODE_REG_OFFSET,
                {{KEYMGR_DPE_ERR_CODE_INVALID_SHADOW_UPDATE_BIT, true}});
  EXPECT_WRITE32(KEYMGR_DPE_ERR_CODE_REG_OFFSET,
                 {{KEYMGR_DPE_ERR_CODE_INVALID_SHADOW_UPDATE_BIT, true}});

  dif_keymgr_dpe_status_codes_t status_codes;
  EXPECT_DIF_OK(dif_keymgr_dpe_get_status_codes(&keymgr_dpe_, &status_codes));
  EXPECT_EQ(status_codes,
            kDifKeymgrDpeStatusCodeIdle | kDifKeymgrDpeStatusCodeInvalidState);
}

TEST_F(GetStatusCodesTest, DoneSuccessWithShadowUpdateError) {
  EXPECT_READ32(KEYMGR_DPE_OP_STATUS_REG_OFFSET,
                KEYMGR_DPE_OP_STATUS_STATUS_VALUE_DONE_SUCCESS);
  EXPECT_WRITE32(KEYMGR_DPE_OP_STATUS_REG_OFFSET,
                 KEYMGR_DPE_OP_STATUS_STATUS_VALUE_DONE_SUCCESS);
  EXPECT_READ32(KEYMGR_DPE_ERR_CODE_REG_OFFSET,
                {{KEYMGR_DPE_ERR_CODE_INVALID_SHADOW_UPDATE_BIT, true}});
  EXPECT_WRITE32(KEYMGR_DPE_ERR_CODE_REG_OFFSET,
                 {{KEYMGR_DPE_ERR_CODE_INVALID_SHADOW_UPDATE_BIT, true}});

  dif_keymgr_dpe_status_codes_t status_codes;
  EXPECT_DIF_OK(dif_keymgr_dpe_get_status_codes(&keymgr_dpe_, &status_codes));
  EXPECT_EQ(status_codes,
            kDifKeymgrDpeStatusCodeIdle | kDifKeymgrDpeStatusCodeInvalidState);
}

TEST_F(GetStatusCodesTest, DoneError) {
  EXPECT_READ32(KEYMGR_DPE_OP_STATUS_REG_OFFSET,
                KEYMGR_DPE_OP_STATUS_STATUS_VALUE_DONE_ERROR);
  EXPECT_WRITE32(KEYMGR_DPE_OP_STATUS_REG_OFFSET,
                 KEYMGR_DPE_OP_STATUS_STATUS_VALUE_DONE_ERROR);
  EXPECT_READ32(KEYMGR_DPE_ERR_CODE_REG_OFFSET,
                {{KEYMGR_DPE_ERR_CODE_INVALID_OP_BIT, true}});
  EXPECT_WRITE32(KEYMGR_DPE_ERR_CODE_REG_OFFSET,
                 {{KEYMGR_DPE_ERR_CODE_INVALID_OP_BIT, true}});

  dif_keymgr_dpe_status_codes_t status_codes;
  EXPECT_DIF_OK(dif_keymgr_dpe_get_status_codes(&keymgr_dpe_, &status_codes));
  EXPECT_EQ(status_codes, kDifKeymgrDpeStatusCodeIdle |
                              kDifKeymgrDpeStatusCodeInvalidOperation);
}

}  // namespace
}  // namespace dif_keymgr_dpe_unittest
