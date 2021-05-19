// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/keymgr.h"

#include <array>
#include <limits>

#include "gtest/gtest.h"
#include "sw/device/silicon_creator/lib/base/mock_abs_mmio.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "keymgr_regs.h"  // Generated.

namespace keymgr_unittest {
namespace {
using ::testing::ElementsAreArray;
using ::testing::Test;

struct SwBindingCfg {
  uint32_t max_key_ver;
  uint32_t sw_binding_value[8];
};

class KeymgrTest : public mask_rom_test::MaskRomTest {
 protected:
  void ExpectStatusCheck(uint32_t op_status, uint32_t km_state,
                         uint32_t err_code) {
    EXPECT_ABS_READ32(mmio_, base_ + KEYMGR_OP_STATUS_REG_OFFSET, op_status);
    EXPECT_ABS_WRITE32(mmio_, base_ + KEYMGR_OP_STATUS_REG_OFFSET, op_status);

    EXPECT_ABS_READ32(mmio_, base_ + KEYMGR_ERR_CODE_REG_OFFSET, err_code);
    EXPECT_ABS_WRITE32(mmio_, base_ + KEYMGR_ERR_CODE_REG_OFFSET, err_code);

    EXPECT_ABS_READ32(mmio_, base_ + KEYMGR_WORKING_STATE_REG_OFFSET, km_state);
  }
  uint32_t base_ = TOP_EARLGREY_KEYMGR_BASE_ADDR;
  SwBindingCfg cfg_ = {
      .max_key_ver = 0xA5A5A5A5,
      .sw_binding_value = {0, 1, 2, 3, 4, 6, 7, 8},
  };
  mask_rom_test::MockAbsMmio mmio_;
};

TEST_F(KeymgrTest, Initialize) {
  ExpectStatusCheck(KEYMGR_OP_STATUS_STATUS_VALUE_IDLE,
                    KEYMGR_WORKING_STATE_STATE_VALUE_RESET,
                    /*err_code=*/0u);

  EXPECT_ABS_WRITE32(mmio_, base_ + KEYMGR_RESEED_INTERVAL_REG_OFFSET, 0u);

  EXPECT_ABS_WRITE32(
      mmio_, base_ + KEYMGR_CONTROL_REG_OFFSET,
      {
          {KEYMGR_CONTROL_START_BIT, true},
          {KEYMGR_CONTROL_DEST_SEL_OFFSET, KEYMGR_CONTROL_DEST_SEL_VALUE_NONE},
          {KEYMGR_CONTROL_OPERATION_OFFSET,
           KEYMGR_CONTROL_OPERATION_VALUE_ADVANCE},
      });

  EXPECT_EQ(keymgr_init(0u), kErrorOk);
}

TEST_F(KeymgrTest, StateAdvanceToCreator) {
  // Simulate an WIP OP status to exercise the polling check, followed by the
  // DONE_SUCCESS expectation.
  EXPECT_ABS_READ32(
      mmio_, base_ + KEYMGR_OP_STATUS_REG_OFFSET,
      {{KEYMGR_OP_STATUS_STATUS_OFFSET, KEYMGR_OP_STATUS_STATUS_VALUE_WIP}});
  EXPECT_ABS_WRITE32(
      mmio_, base_ + KEYMGR_OP_STATUS_REG_OFFSET,
      {{KEYMGR_OP_STATUS_STATUS_OFFSET, KEYMGR_OP_STATUS_STATUS_VALUE_WIP}});
  ExpectStatusCheck(KEYMGR_OP_STATUS_STATUS_VALUE_DONE_SUCCESS,
                    KEYMGR_WORKING_STATE_STATE_VALUE_INIT,
                    /*err_code=*/0u);

  EXPECT_ABS_WRITE32(mmio_, base_ + KEYMGR_SW_BINDING_0_REG_OFFSET,
                     cfg_.sw_binding_value[0]);
  EXPECT_ABS_WRITE32(mmio_, base_ + KEYMGR_SW_BINDING_1_REG_OFFSET,
                     cfg_.sw_binding_value[1]);
  EXPECT_ABS_WRITE32(mmio_, base_ + KEYMGR_SW_BINDING_2_REG_OFFSET,
                     cfg_.sw_binding_value[2]);
  EXPECT_ABS_WRITE32(mmio_, base_ + KEYMGR_SW_BINDING_3_REG_OFFSET,
                     cfg_.sw_binding_value[3]);
  EXPECT_ABS_WRITE32(mmio_, base_ + KEYMGR_SW_BINDING_4_REG_OFFSET,
                     cfg_.sw_binding_value[4]);
  EXPECT_ABS_WRITE32(mmio_, base_ + KEYMGR_SW_BINDING_5_REG_OFFSET,
                     cfg_.sw_binding_value[5]);
  EXPECT_ABS_WRITE32(mmio_, base_ + KEYMGR_SW_BINDING_6_REG_OFFSET,
                     cfg_.sw_binding_value[6]);
  EXPECT_ABS_WRITE32(mmio_, base_ + KEYMGR_SW_BINDING_7_REG_OFFSET,
                     cfg_.sw_binding_value[7]);
  EXPECT_ABS_WRITE32(mmio_, base_ + KEYMGR_SW_BINDING_REGWEN_REG_OFFSET, 0);

  EXPECT_ABS_WRITE32(mmio_, base_ + KEYMGR_MAX_CREATOR_KEY_VER_REG_OFFSET,
                     cfg_.max_key_ver);
  EXPECT_ABS_WRITE32(mmio_,
                     base_ + KEYMGR_MAX_CREATOR_KEY_VER_REGWEN_REG_OFFSET, 0);

  EXPECT_ABS_WRITE32(
      mmio_, base_ + KEYMGR_CONTROL_REG_OFFSET,
      {
          {KEYMGR_CONTROL_START_BIT, true},
          {KEYMGR_CONTROL_DEST_SEL_OFFSET, KEYMGR_CONTROL_DEST_SEL_VALUE_NONE},
          {KEYMGR_CONTROL_OPERATION_OFFSET,
           KEYMGR_CONTROL_OPERATION_VALUE_ADVANCE},
      });

  EXPECT_EQ(
      keymgr_state_advance_to_creator(cfg_.sw_binding_value, cfg_.max_key_ver),
      kErrorOk);
}

TEST_F(KeymgrTest, StateAdvanceToCreatorInvalid) {
  // Any state different than INIT is expected to fail.
  ExpectStatusCheck(KEYMGR_OP_STATUS_STATUS_VALUE_DONE_SUCCESS,
                    KEYMGR_WORKING_STATE_STATE_VALUE_RESET,
                    /*err_code=*/0u);
  EXPECT_EQ(
      keymgr_state_advance_to_creator(cfg_.sw_binding_value, cfg_.max_key_ver),
      kErrorKeymgrInternal);

  // Any non-idle status is expected to fail.
  ExpectStatusCheck(KEYMGR_OP_STATUS_STATUS_VALUE_DONE_ERROR,
                    KEYMGR_WORKING_STATE_STATE_VALUE_INIT,
                    /*err_code=*/0u);
  EXPECT_EQ(
      keymgr_state_advance_to_creator(cfg_.sw_binding_value, cfg_.max_key_ver),
      kErrorKeymgrInternal);
}

TEST_F(KeymgrTest, StateCreatorCheck) {
  ExpectStatusCheck(KEYMGR_OP_STATUS_STATUS_VALUE_DONE_SUCCESS,
                    KEYMGR_WORKING_STATE_STATE_VALUE_CREATOR_ROOT_KEY,
                    /*err_code=*/0u);
  EXPECT_EQ(keymgr_state_creator_check(), kErrorOk);
}

TEST_F(KeymgrTest, StateCreatorCheckInvalidResponse) {
  // Any state different than CREATOR_ROOT is expected to fail.
  ExpectStatusCheck(KEYMGR_OP_STATUS_STATUS_VALUE_DONE_SUCCESS,
                    KEYMGR_WORKING_STATE_STATE_VALUE_INVALID,
                    /*err_code=*/0u);
  EXPECT_EQ(keymgr_state_creator_check(), kErrorKeymgrInternal);

  // Any non-idle status is expected to fail.
  ExpectStatusCheck(KEYMGR_OP_STATUS_STATUS_VALUE_DONE_ERROR,
                    KEYMGR_WORKING_STATE_STATE_VALUE_CREATOR_ROOT_KEY,
                    /*err_code=*/0u);
  EXPECT_EQ(keymgr_state_creator_check(), kErrorKeymgrInternal);
}

}  // namespace
}  // namespace keymgr_unittest
