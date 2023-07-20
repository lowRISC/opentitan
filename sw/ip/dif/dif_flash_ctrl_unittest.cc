// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_flash_ctrl.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "flash_ctrl_regs.h"  // Generated.

namespace dif_flash_ctrl_unittest {
namespace {
using mock_mmio::MmioTest;
using mock_mmio::MockDevice;
using testing::Test;

class FlashCtrlTest : public Test, public MmioTest {
 protected:
  void SetUp() {
    ASSERT_DIF_OK(dif_flash_ctrl_init_state(&dif_flash_ctrl_, dev().region()));
  }

  dif_flash_ctrl_state_t dif_flash_ctrl_;
};

TEST_F(FlashCtrlTest, NullArgs) {
  dif_toggle_t toggle_arg{};
  EXPECT_DIF_BADARG(dif_flash_ctrl_set_flash_enablement(nullptr, toggle_arg));
  EXPECT_DIF_BADARG(dif_flash_ctrl_get_flash_enablement(nullptr, &toggle_arg));
  EXPECT_DIF_BADARG(
      dif_flash_ctrl_get_flash_enablement(&dif_flash_ctrl_, nullptr));

  EXPECT_DIF_BADARG(
      dif_flash_ctrl_set_exec_enablement(nullptr, kDifToggleEnabled));
  EXPECT_DIF_BADARG(dif_flash_ctrl_get_exec_enablement(nullptr, &toggle_arg));
  EXPECT_DIF_BADARG(
      dif_flash_ctrl_get_exec_enablement(&dif_flash_ctrl_, nullptr));

  EXPECT_DIF_BADARG(dif_flash_ctrl_start_controller_init(nullptr));

  dif_flash_ctrl_status_t status_arg{};
  EXPECT_DIF_BADARG(dif_flash_ctrl_get_status(nullptr, &status_arg));
  EXPECT_DIF_BADARG(dif_flash_ctrl_get_status(&dif_flash_ctrl_, nullptr));

  dif_flash_ctrl_prog_capabilities_t caps_arg{};
  EXPECT_DIF_BADARG(dif_flash_ctrl_get_allowed_prog_types(nullptr, &caps_arg));
  EXPECT_DIF_BADARG(
      dif_flash_ctrl_get_allowed_prog_types(&dif_flash_ctrl_, nullptr));
  EXPECT_DIF_BADARG(dif_flash_ctrl_disallow_prog_types(nullptr, caps_arg));

  EXPECT_DIF_BADARG(dif_flash_ctrl_start(nullptr, {}));
  EXPECT_DIF_BADARG(dif_flash_ctrl_start_unsafe(nullptr, {}));

  bool bool_arg = false;
  EXPECT_DIF_BADARG(dif_flash_ctrl_suspend_erase(nullptr));
  EXPECT_DIF_BADARG(
      dif_flash_ctrl_get_erase_suspend_status(&dif_flash_ctrl_, nullptr));
  EXPECT_DIF_BADARG(
      dif_flash_ctrl_get_erase_suspend_status(nullptr, &bool_arg));

  uint32_t data_arg = 0;
  EXPECT_DIF_BADARG(
      dif_flash_ctrl_prog_fifo_push_unsafe(nullptr, 1, &data_arg));
  EXPECT_DIF_BADARG(
      dif_flash_ctrl_prog_fifo_push_unsafe(&dif_flash_ctrl_, 1, nullptr));
  EXPECT_DIF_BADARG(dif_flash_ctrl_prog_fifo_push(nullptr, 1, &data_arg));
  EXPECT_DIF_BADARG(
      dif_flash_ctrl_prog_fifo_push(&dif_flash_ctrl_, 1, nullptr));
  EXPECT_DIF_BADARG(dif_flash_ctrl_read_fifo_pop_unsafe(nullptr, 1, &data_arg));
  EXPECT_DIF_BADARG(
      dif_flash_ctrl_read_fifo_pop_unsafe(&dif_flash_ctrl_, 1, nullptr));
  EXPECT_DIF_BADARG(dif_flash_ctrl_read_fifo_pop(nullptr, 1, &data_arg));
  EXPECT_DIF_BADARG(dif_flash_ctrl_read_fifo_pop(&dif_flash_ctrl_, 1, nullptr));

  dif_flash_ctrl_error_t error_arg{};
  EXPECT_DIF_BADARG(dif_flash_ctrl_get_error_codes(nullptr, &error_arg));
  EXPECT_DIF_BADARG(dif_flash_ctrl_get_error_codes(&dif_flash_ctrl_, nullptr));
  EXPECT_DIF_BADARG(dif_flash_ctrl_clear_error_codes(nullptr, {}));

  dif_flash_ctrl_output_t output_arg{};
  EXPECT_DIF_BADARG(dif_flash_ctrl_end(nullptr, &output_arg));
  EXPECT_DIF_BADARG(dif_flash_ctrl_end(&dif_flash_ctrl_, nullptr));

  EXPECT_DIF_BADARG(dif_flash_ctrl_set_data_region_enablement(
      nullptr, /*region=*/0, toggle_arg));
  EXPECT_DIF_BADARG(dif_flash_ctrl_get_data_region_enablement(
      nullptr, /*region=*/0, &toggle_arg));
  EXPECT_DIF_BADARG(dif_flash_ctrl_get_data_region_enablement(&dif_flash_ctrl_,
                                                              /*region=*/0,
                                                              nullptr));

  EXPECT_DIF_BADARG(
      dif_flash_ctrl_set_info_region_enablement(nullptr, {}, toggle_arg));
  EXPECT_DIF_BADARG(
      dif_flash_ctrl_get_info_region_enablement(nullptr, {}, &toggle_arg));
  EXPECT_DIF_BADARG(
      dif_flash_ctrl_get_info_region_enablement(&dif_flash_ctrl_, {}, nullptr));

  dif_flash_ctrl_region_properties_t mp_arg{};
  EXPECT_DIF_BADARG(
      dif_flash_ctrl_set_default_region_properties(nullptr, mp_arg));
  EXPECT_DIF_BADARG(
      dif_flash_ctrl_get_default_region_properties(nullptr, &mp_arg));
  EXPECT_DIF_BADARG(
      dif_flash_ctrl_get_default_region_properties(&dif_flash_ctrl_, nullptr));

  dif_flash_ctrl_data_region_properties_t data_mp_arg;
  EXPECT_DIF_BADARG(
      dif_flash_ctrl_set_data_region_properties(nullptr, 0, data_mp_arg));
  EXPECT_DIF_BADARG(
      dif_flash_ctrl_get_data_region_properties(nullptr, 0, &data_mp_arg));
  EXPECT_DIF_BADARG(
      dif_flash_ctrl_get_data_region_properties(&dif_flash_ctrl_, 0, nullptr));

  EXPECT_DIF_BADARG(
      dif_flash_ctrl_set_info_region_properties(nullptr, {}, mp_arg));
  EXPECT_DIF_BADARG(
      dif_flash_ctrl_get_info_region_properties(nullptr, {}, &mp_arg));
  EXPECT_DIF_BADARG(
      dif_flash_ctrl_get_info_region_properties(&dif_flash_ctrl_, {}, nullptr));

  EXPECT_DIF_BADARG(dif_flash_ctrl_lock_data_region_properties(nullptr, 0));
  EXPECT_DIF_BADARG(dif_flash_ctrl_lock_info_region_properties(nullptr, {}));

  EXPECT_DIF_BADARG(
      dif_flash_ctrl_data_region_is_locked(nullptr, 0, &bool_arg));
  EXPECT_DIF_BADARG(
      dif_flash_ctrl_data_region_is_locked(&dif_flash_ctrl_, 0, nullptr));
  EXPECT_DIF_BADARG(
      dif_flash_ctrl_info_region_is_locked(nullptr, {}, &bool_arg));
  EXPECT_DIF_BADARG(
      dif_flash_ctrl_info_region_is_locked(&dif_flash_ctrl_, {}, nullptr));

  EXPECT_DIF_BADARG(dif_flash_ctrl_set_bank_erase_enablement(
      nullptr, /*region=*/0, toggle_arg));
  EXPECT_DIF_BADARG(dif_flash_ctrl_get_bank_erase_enablement(
      nullptr, /*region=*/0, &toggle_arg));
  EXPECT_DIF_BADARG(dif_flash_ctrl_get_bank_erase_enablement(&dif_flash_ctrl_,
                                                             /*region=*/0,
                                                             nullptr));

  EXPECT_DIF_BADARG(dif_flash_ctrl_lock_bank_configuration(nullptr));
  EXPECT_DIF_BADARG(
      dif_flash_ctrl_bank_configuration_is_locked(nullptr, &bool_arg));
  EXPECT_DIF_BADARG(
      dif_flash_ctrl_bank_configuration_is_locked(&dif_flash_ctrl_, nullptr));

  EXPECT_DIF_BADARG(dif_flash_ctrl_set_prog_fifo_watermark(nullptr, 0));
  EXPECT_DIF_BADARG(dif_flash_ctrl_set_read_fifo_watermark(nullptr, 0));
  EXPECT_DIF_BADARG(
      dif_flash_ctrl_get_fifo_watermarks(nullptr, nullptr, nullptr));

  EXPECT_DIF_BADARG(dif_flash_ctrl_reset_fifos(nullptr));

  dif_flash_ctrl_faults_t faults_arg{};
  EXPECT_DIF_BADARG(dif_flash_ctrl_get_faults(nullptr, &faults_arg));
  EXPECT_DIF_BADARG(dif_flash_ctrl_get_faults(&dif_flash_ctrl_, nullptr));

  dif_flash_ctrl_ecc_errors_t ecc_errors_arg{};
  EXPECT_DIF_BADARG(dif_flash_ctrl_get_ecc_errors(nullptr, 0, &ecc_errors_arg));
  EXPECT_DIF_BADARG(
      dif_flash_ctrl_get_ecc_errors(&dif_flash_ctrl_, 0, nullptr));

  dif_flash_ctrl_phy_status_t phy_status_arg{};
  EXPECT_DIF_BADARG(dif_flash_ctrl_get_phy_status(nullptr, &phy_status_arg));
  EXPECT_DIF_BADARG(dif_flash_ctrl_get_phy_status(&dif_flash_ctrl_, nullptr));

  uint32_t scratch_arg = 0;
  EXPECT_DIF_BADARG(dif_flash_ctrl_set_scratch(nullptr, scratch_arg));
  EXPECT_DIF_BADARG(dif_flash_ctrl_get_scratch(nullptr, &scratch_arg));
  EXPECT_DIF_BADARG(dif_flash_ctrl_get_scratch(&dif_flash_ctrl_, nullptr));
}

TEST_F(FlashCtrlTest, EnableFlash) {
  dif_toggle_t toggle;
  EXPECT_WRITE32(FLASH_CTRL_DIS_REG_OFFSET, kMultiBitBool4True);
  EXPECT_DIF_OK(dif_flash_ctrl_set_flash_enablement(&dif_flash_ctrl_,
                                                    kDifToggleDisabled));
  EXPECT_READ32(FLASH_CTRL_DIS_REG_OFFSET, kMultiBitBool4True);
  EXPECT_DIF_OK(dif_flash_ctrl_get_flash_enablement(&dif_flash_ctrl_, &toggle));
  EXPECT_EQ(toggle, kDifToggleDisabled);

  EXPECT_WRITE32(FLASH_CTRL_DIS_REG_OFFSET, kMultiBitBool4False);
  EXPECT_DIF_OK(
      dif_flash_ctrl_set_flash_enablement(&dif_flash_ctrl_, kDifToggleEnabled));
  EXPECT_READ32(FLASH_CTRL_DIS_REG_OFFSET, kMultiBitBool4False);
  EXPECT_DIF_OK(dif_flash_ctrl_get_flash_enablement(&dif_flash_ctrl_, &toggle));
  EXPECT_EQ(toggle, kDifToggleEnabled);
}

TEST_F(FlashCtrlTest, EnableFetch) {
  dif_toggle_t toggle;
  EXPECT_WRITE32(FLASH_CTRL_EXEC_REG_OFFSET, 0);
  EXPECT_DIF_OK(
      dif_flash_ctrl_set_exec_enablement(&dif_flash_ctrl_, kDifToggleDisabled));
  EXPECT_READ32(FLASH_CTRL_EXEC_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_flash_ctrl_get_exec_enablement(&dif_flash_ctrl_, &toggle));
  EXPECT_EQ(toggle, kDifToggleDisabled);

  EXPECT_WRITE32(FLASH_CTRL_EXEC_REG_OFFSET, FLASH_CTRL_PARAM_EXEC_EN);
  EXPECT_DIF_OK(
      dif_flash_ctrl_set_exec_enablement(&dif_flash_ctrl_, kDifToggleEnabled));
  EXPECT_READ32(FLASH_CTRL_EXEC_REG_OFFSET, FLASH_CTRL_PARAM_EXEC_EN);
  EXPECT_DIF_OK(dif_flash_ctrl_get_exec_enablement(&dif_flash_ctrl_, &toggle));
  EXPECT_EQ(toggle, kDifToggleEnabled);
}

TEST_F(FlashCtrlTest, ControllerInit) {
  EXPECT_READ32(FLASH_CTRL_INIT_REG_OFFSET, 0);
  EXPECT_WRITE32(FLASH_CTRL_INIT_REG_OFFSET, {{FLASH_CTRL_INIT_VAL_BIT, 1}});
  EXPECT_DIF_OK(dif_flash_ctrl_start_controller_init(&dif_flash_ctrl_));

  EXPECT_READ32(FLASH_CTRL_INIT_REG_OFFSET, {{FLASH_CTRL_INIT_VAL_BIT, 1}});
  EXPECT_EQ(dif_flash_ctrl_start_controller_init(&dif_flash_ctrl_), kDifError);

  dif_flash_ctrl_status_t status;
  EXPECT_READ32(FLASH_CTRL_STATUS_REG_OFFSET,
                {
                    {FLASH_CTRL_STATUS_INIT_WIP_BIT, 1},
                });
  EXPECT_DIF_OK(dif_flash_ctrl_get_status(&dif_flash_ctrl_, &status));
  EXPECT_EQ(status.controller_init_wip, 1);

  EXPECT_READ32(FLASH_CTRL_STATUS_REG_OFFSET,
                {
                    {FLASH_CTRL_STATUS_INIT_WIP_BIT, 0},
                });
  EXPECT_DIF_OK(dif_flash_ctrl_get_status(&dif_flash_ctrl_, &status));
  EXPECT_EQ(status.controller_init_wip, 0);
}

TEST_F(FlashCtrlTest, SetProgPermissions) {
  dif_flash_ctrl_prog_capabilities prog_caps = {
      .normal_prog_type = 0,
      .repair_prog_type = 1,
  };

  EXPECT_READ32(FLASH_CTRL_CTRL_REGWEN_REG_OFFSET,
                {{FLASH_CTRL_CTRL_REGWEN_EN_BIT, 1}});

  EXPECT_WRITE32(FLASH_CTRL_PROG_TYPE_EN_REG_OFFSET,
                 {
                     {FLASH_CTRL_PROG_TYPE_EN_NORMAL_BIT, 1},
                     {FLASH_CTRL_PROG_TYPE_EN_REPAIR_BIT, 0},
                 });
  EXPECT_DIF_OK(
      dif_flash_ctrl_disallow_prog_types(&dif_flash_ctrl_, prog_caps));
  EXPECT_READ32(FLASH_CTRL_PROG_TYPE_EN_REG_OFFSET,
                {
                    {FLASH_CTRL_PROG_TYPE_EN_NORMAL_BIT, 1},
                    {FLASH_CTRL_PROG_TYPE_EN_REPAIR_BIT, 0},
                });
  EXPECT_DIF_OK(
      dif_flash_ctrl_get_allowed_prog_types(&dif_flash_ctrl_, &prog_caps));
  EXPECT_EQ(prog_caps.normal_prog_type, 1);
  EXPECT_EQ(prog_caps.repair_prog_type, 0);

  prog_caps.normal_prog_type = 1;
  prog_caps.repair_prog_type = 0;

  EXPECT_READ32(FLASH_CTRL_CTRL_REGWEN_REG_OFFSET,
                {{FLASH_CTRL_CTRL_REGWEN_EN_BIT, 1}});

  EXPECT_WRITE32(FLASH_CTRL_PROG_TYPE_EN_REG_OFFSET,
                 {
                     {FLASH_CTRL_PROG_TYPE_EN_NORMAL_BIT, 0},
                     {FLASH_CTRL_PROG_TYPE_EN_REPAIR_BIT, 1},
                 });
  EXPECT_DIF_OK(
      dif_flash_ctrl_disallow_prog_types(&dif_flash_ctrl_, prog_caps));
  EXPECT_READ32(FLASH_CTRL_PROG_TYPE_EN_REG_OFFSET,
                {
                    {FLASH_CTRL_PROG_TYPE_EN_NORMAL_BIT, 0},
                    {FLASH_CTRL_PROG_TYPE_EN_REPAIR_BIT, 1},
                });
  EXPECT_DIF_OK(
      dif_flash_ctrl_get_allowed_prog_types(&dif_flash_ctrl_, &prog_caps));
  EXPECT_EQ(prog_caps.normal_prog_type, 0);
  EXPECT_EQ(prog_caps.repair_prog_type, 1);
}

TEST_F(FlashCtrlTest, ReadTransaction) {
  dif_flash_ctrl_transaction_t transaction = {
      .op = kDifFlashCtrlOpRead,
      .partition_type = kDifFlashCtrlPartitionTypeInfo,
      .partition_id = 1,
      .byte_address = 0x80,
      .word_count = 0x20,
  };

  // Read FIFO not empty
  EXPECT_READ32(FLASH_CTRL_STATUS_REG_OFFSET,
                {
                    {FLASH_CTRL_STATUS_RD_FULL_BIT, 0},
                    {FLASH_CTRL_STATUS_RD_EMPTY_BIT, 0},
                    {FLASH_CTRL_STATUS_PROG_EMPTY_BIT, 1},
                });
  EXPECT_EQ(dif_flash_ctrl_start(&dif_flash_ctrl_, transaction),
            kDifIpFifoFull);
  // Control register not writable
  EXPECT_READ32(FLASH_CTRL_STATUS_REG_OFFSET,
                {
                    {FLASH_CTRL_STATUS_RD_FULL_BIT, 0},
                    {FLASH_CTRL_STATUS_RD_EMPTY_BIT, 1},
                    {FLASH_CTRL_STATUS_PROG_EMPTY_BIT, 1},
                });
  EXPECT_READ32(FLASH_CTRL_CTRL_REGWEN_REG_OFFSET,
                {{FLASH_CTRL_CTRL_REGWEN_EN_BIT, 0}});
  EXPECT_EQ(dif_flash_ctrl_start(&dif_flash_ctrl_, transaction),
            kDifUnavailable);

  // Read transaction setup is successful
  EXPECT_READ32(FLASH_CTRL_STATUS_REG_OFFSET,
                {
                    {FLASH_CTRL_STATUS_RD_FULL_BIT, 0},
                    {FLASH_CTRL_STATUS_RD_EMPTY_BIT, 1},
                    {FLASH_CTRL_STATUS_PROG_EMPTY_BIT, 1},
                });
  EXPECT_READ32(FLASH_CTRL_CTRL_REGWEN_REG_OFFSET,
                {{FLASH_CTRL_CTRL_REGWEN_EN_BIT, 1}});
  EXPECT_WRITE32(
      FLASH_CTRL_CONTROL_REG_OFFSET,
      {
          {FLASH_CTRL_CONTROL_OP_OFFSET, FLASH_CTRL_CONTROL_OP_VALUE_READ},
          {FLASH_CTRL_CONTROL_PARTITION_SEL_BIT, 1},
          {FLASH_CTRL_CONTROL_INFO_SEL_OFFSET, 1},
          {FLASH_CTRL_CONTROL_NUM_OFFSET, 0x20 - 1},
      });
  EXPECT_WRITE32(FLASH_CTRL_ADDR_REG_OFFSET, 0x80);
  EXPECT_WRITE32(
      FLASH_CTRL_CONTROL_REG_OFFSET,
      {
          {FLASH_CTRL_CONTROL_START_BIT, 1},
          {FLASH_CTRL_CONTROL_OP_OFFSET, FLASH_CTRL_CONTROL_OP_VALUE_READ},
          {FLASH_CTRL_CONTROL_PARTITION_SEL_BIT, 1},
          {FLASH_CTRL_CONTROL_INFO_SEL_OFFSET, 1},
          {FLASH_CTRL_CONTROL_NUM_OFFSET, 0x20 - 1},
      });
  EXPECT_DIF_OK(dif_flash_ctrl_start(&dif_flash_ctrl_, transaction));
  EXPECT_TRUE(dif_flash_ctrl_.transaction_pending);

  // Read the data
  uint32_t data[0x20];
  EXPECT_READ32(
      FLASH_CTRL_CONTROL_REG_OFFSET,
      {
          {FLASH_CTRL_CONTROL_START_BIT, 1},
          {FLASH_CTRL_CONTROL_OP_OFFSET, FLASH_CTRL_CONTROL_OP_VALUE_READ},
          {FLASH_CTRL_CONTROL_PARTITION_SEL_BIT, 1},
          {FLASH_CTRL_CONTROL_INFO_SEL_OFFSET, 1},
          {FLASH_CTRL_CONTROL_NUM_OFFSET, 0x20 - 1},
      });
  for (uint32_t i = 0; i < 0x20; ++i) {
    EXPECT_READ32(FLASH_CTRL_RD_FIFO_REG_OFFSET, i);
  }
  EXPECT_DIF_OK(dif_flash_ctrl_read_fifo_pop(&dif_flash_ctrl_, 0x20, data));
  for (uint32_t i = 0; i < 0x20; i++) {
    EXPECT_EQ(data[i], i);
  }

  // Complete the transaction (with meaningless error code return)
  dif_flash_ctrl_output_t output;
  EXPECT_READ32(FLASH_CTRL_OP_STATUS_REG_OFFSET,
                {
                    {FLASH_CTRL_OP_STATUS_DONE_BIT, 0},
                    {FLASH_CTRL_OP_STATUS_ERR_BIT, 0},
                });
  EXPECT_EQ(dif_flash_ctrl_end(&dif_flash_ctrl_, &output), kDifUnavailable);
  EXPECT_READ32(FLASH_CTRL_OP_STATUS_REG_OFFSET,
                {
                    {FLASH_CTRL_OP_STATUS_DONE_BIT, 1},
                    {FLASH_CTRL_OP_STATUS_ERR_BIT, 0},
                });
  EXPECT_WRITE32(FLASH_CTRL_OP_STATUS_REG_OFFSET, 0);
  EXPECT_READ32(FLASH_CTRL_ERR_CODE_REG_OFFSET,
                {
                    {FLASH_CTRL_ERR_CODE_MP_ERR_BIT, 1},
                    {FLASH_CTRL_ERR_CODE_RD_ERR_BIT, 0},
                    {FLASH_CTRL_ERR_CODE_PROG_WIN_ERR_BIT, 1},
                    {FLASH_CTRL_ERR_CODE_PROG_TYPE_ERR_BIT, 0},
                    {FLASH_CTRL_ERR_CODE_UPDATE_ERR_BIT, 0},
                });
  EXPECT_READ32(FLASH_CTRL_ERR_ADDR_REG_OFFSET, 0x12345678u);
  EXPECT_DIF_OK(dif_flash_ctrl_end(&dif_flash_ctrl_, &output));
  EXPECT_FALSE(dif_flash_ctrl_.transaction_pending);
  EXPECT_EQ(output.operation_done, 1);
  EXPECT_EQ(output.operation_error, 0);
  EXPECT_EQ(output.error_code.address, 0x12345678u);
  EXPECT_EQ(output.error_code.codes.memory_properties_error, 1);
  EXPECT_EQ(output.error_code.codes.read_error, 0);
  EXPECT_EQ(output.error_code.codes.prog_window_error, 1);
  EXPECT_EQ(output.error_code.codes.prog_type_error, 0);
  EXPECT_EQ(output.error_code.codes.shadow_register_error, 0);
}

TEST_F(FlashCtrlTest, ProgramTransaction) {
  dif_flash_ctrl_transaction_t transaction = {
      .op = kDifFlashCtrlOpProgramRepair,
      .partition_type = kDifFlashCtrlPartitionTypeData,
      .partition_id = 0,
      .byte_address = 0x1800,
      .word_count = 0x16,
  };

  // Prog FIFO not empty
  EXPECT_READ32(FLASH_CTRL_STATUS_REG_OFFSET,
                {
                    {FLASH_CTRL_STATUS_RD_EMPTY_BIT, 1},
                    {FLASH_CTRL_STATUS_PROG_FULL_BIT, 0},
                    {FLASH_CTRL_STATUS_PROG_EMPTY_BIT, 0},
                });
  EXPECT_EQ(dif_flash_ctrl_start(&dif_flash_ctrl_, transaction),
            kDifIpFifoFull);
  // Control register not writable
  EXPECT_READ32(FLASH_CTRL_STATUS_REG_OFFSET,
                {
                    {FLASH_CTRL_STATUS_RD_EMPTY_BIT, 1},
                    {FLASH_CTRL_STATUS_PROG_FULL_BIT, 0},
                    {FLASH_CTRL_STATUS_PROG_EMPTY_BIT, 1},
                });
  EXPECT_READ32(FLASH_CTRL_CTRL_REGWEN_REG_OFFSET,
                {{FLASH_CTRL_CTRL_REGWEN_EN_BIT, 0}});
  EXPECT_EQ(dif_flash_ctrl_start(&dif_flash_ctrl_, transaction),
            kDifUnavailable);

  // Prog transaction setup is successful
  EXPECT_READ32(FLASH_CTRL_STATUS_REG_OFFSET,
                {
                    {FLASH_CTRL_STATUS_RD_EMPTY_BIT, 1},
                    {FLASH_CTRL_STATUS_PROG_FULL_BIT, 0},
                    {FLASH_CTRL_STATUS_PROG_EMPTY_BIT, 1},
                });
  EXPECT_READ32(FLASH_CTRL_CTRL_REGWEN_REG_OFFSET,
                {{FLASH_CTRL_CTRL_REGWEN_EN_BIT, 1}});
  EXPECT_WRITE32(
      FLASH_CTRL_CONTROL_REG_OFFSET,
      {
          {FLASH_CTRL_CONTROL_OP_OFFSET, FLASH_CTRL_CONTROL_OP_VALUE_PROG},
          {FLASH_CTRL_CONTROL_PARTITION_SEL_BIT, 0},
          {FLASH_CTRL_CONTROL_PROG_SEL_BIT, 1},
          {FLASH_CTRL_CONTROL_NUM_OFFSET, 0x16 - 1},
      });
  EXPECT_WRITE32(FLASH_CTRL_ADDR_REG_OFFSET, 0x1800);
  EXPECT_WRITE32(
      FLASH_CTRL_CONTROL_REG_OFFSET,
      {
          {FLASH_CTRL_CONTROL_START_BIT, 1},
          {FLASH_CTRL_CONTROL_OP_OFFSET, FLASH_CTRL_CONTROL_OP_VALUE_PROG},
          {FLASH_CTRL_CONTROL_PARTITION_SEL_BIT, 0},
          {FLASH_CTRL_CONTROL_PROG_SEL_BIT, 1},
          {FLASH_CTRL_CONTROL_NUM_OFFSET, 0x16 - 1},
      });
  EXPECT_DIF_OK(dif_flash_ctrl_start(&dif_flash_ctrl_, transaction));
  EXPECT_TRUE(dif_flash_ctrl_.transaction_pending);

  // Write out the data
  uint32_t data[0x16];
  EXPECT_READ32(
      FLASH_CTRL_CONTROL_REG_OFFSET,
      {
          {FLASH_CTRL_CONTROL_START_BIT, 1},
          {FLASH_CTRL_CONTROL_OP_OFFSET, FLASH_CTRL_CONTROL_OP_VALUE_PROG},
          {FLASH_CTRL_CONTROL_PARTITION_SEL_BIT, 0},
          {FLASH_CTRL_CONTROL_PROG_SEL_BIT, 1},
          {FLASH_CTRL_CONTROL_NUM_OFFSET, 0x16 - 1},
      });
  for (uint32_t i = 0; i < 0x16; ++i) {
    data[i] = i;
    EXPECT_WRITE32(FLASH_CTRL_PROG_FIFO_REG_OFFSET, i);
  }
  EXPECT_DIF_OK(dif_flash_ctrl_prog_fifo_push(&dif_flash_ctrl_, 0x16, data));

  // Complete the transaction (with meaningless error code return)
  dif_flash_ctrl_output_t output;
  EXPECT_READ32(FLASH_CTRL_OP_STATUS_REG_OFFSET,
                {
                    {FLASH_CTRL_OP_STATUS_DONE_BIT, 0},
                    {FLASH_CTRL_OP_STATUS_ERR_BIT, 0},
                });
  EXPECT_EQ(dif_flash_ctrl_end(&dif_flash_ctrl_, &output), kDifUnavailable);
  EXPECT_READ32(FLASH_CTRL_OP_STATUS_REG_OFFSET,
                {
                    {FLASH_CTRL_OP_STATUS_DONE_BIT, 1},
                    {FLASH_CTRL_OP_STATUS_ERR_BIT, 0},
                });
  EXPECT_WRITE32(FLASH_CTRL_OP_STATUS_REG_OFFSET, 0);
  EXPECT_READ32(FLASH_CTRL_ERR_CODE_REG_OFFSET,
                {
                    {FLASH_CTRL_ERR_CODE_MP_ERR_BIT, 0},
                    {FLASH_CTRL_ERR_CODE_RD_ERR_BIT, 0},
                    {FLASH_CTRL_ERR_CODE_PROG_WIN_ERR_BIT, 1},
                    {FLASH_CTRL_ERR_CODE_PROG_TYPE_ERR_BIT, 1},
                    {FLASH_CTRL_ERR_CODE_UPDATE_ERR_BIT, 1},
                });
  EXPECT_READ32(FLASH_CTRL_ERR_ADDR_REG_OFFSET, 0x87654321u);
  EXPECT_DIF_OK(dif_flash_ctrl_end(&dif_flash_ctrl_, &output));
  EXPECT_FALSE(dif_flash_ctrl_.transaction_pending);
  EXPECT_EQ(output.operation_done, 1);
  EXPECT_EQ(output.operation_error, 0);
  EXPECT_EQ(output.error_code.address, 0x87654321u);
  EXPECT_EQ(output.error_code.codes.memory_properties_error, 0);
  EXPECT_EQ(output.error_code.codes.read_error, 0);
  EXPECT_EQ(output.error_code.codes.prog_window_error, 1);
  EXPECT_EQ(output.error_code.codes.prog_type_error, 1);
  EXPECT_EQ(output.error_code.codes.shadow_register_error, 1);
}

TEST_F(FlashCtrlTest, SuspendErase) {
  EXPECT_WRITE32(FLASH_CTRL_ERASE_SUSPEND_REG_OFFSET,
                 {
                     {FLASH_CTRL_ERASE_SUSPEND_REQ_BIT, 1},
                 });
  EXPECT_DIF_OK(dif_flash_ctrl_suspend_erase(&dif_flash_ctrl_));

  bool erase_suspend_status;
  EXPECT_READ32(FLASH_CTRL_ERASE_SUSPEND_REG_OFFSET,
                {
                    {FLASH_CTRL_ERASE_SUSPEND_REQ_BIT, 1},
                });
  EXPECT_DIF_OK(dif_flash_ctrl_get_erase_suspend_status(&dif_flash_ctrl_,
                                                        &erase_suspend_status));
  EXPECT_TRUE(erase_suspend_status);

  EXPECT_READ32(FLASH_CTRL_ERASE_SUSPEND_REG_OFFSET,
                {
                    {FLASH_CTRL_ERASE_SUSPEND_REQ_BIT, 0},
                });
  EXPECT_DIF_OK(dif_flash_ctrl_get_erase_suspend_status(&dif_flash_ctrl_,
                                                        &erase_suspend_status));
  EXPECT_FALSE(erase_suspend_status);
}

TEST_F(FlashCtrlTest, ConfigureDataRegion) {
  // Uses a few different regions throughout to test the addressing

  // Check whether the region is enabled
  dif_toggle_t toggle;
  EXPECT_READ32(
      FLASH_CTRL_MP_REGION_CFG_4_REG_OFFSET,
      {
          {FLASH_CTRL_MP_REGION_CFG_4_EN_4_OFFSET, kMultiBitBool4False},
      });
  EXPECT_DIF_OK(
      dif_flash_ctrl_get_data_region_enablement(&dif_flash_ctrl_, 4, &toggle));
  EXPECT_EQ(toggle, kDifToggleDisabled);

  // Check if the region is locked
  bool locked;
  EXPECT_READ32(FLASH_CTRL_REGION_CFG_REGWEN_3_REG_OFFSET,
                {{FLASH_CTRL_REGION_CFG_REGWEN_3_REGION_3_BIT, 1}});
  EXPECT_DIF_OK(
      dif_flash_ctrl_data_region_is_locked(&dif_flash_ctrl_, 3, &locked));
  EXPECT_FALSE(locked);

  // Configure the region
  dif_flash_ctrl_data_region_properties_t data_mp = {
      .base = 0x48,
      .size = 0x9a,
      .properties =
          {
              .rd_en = kMultiBitBool4False,
              .prog_en = kMultiBitBool4True,
              .erase_en = kMultiBitBool4True,
              .scramble_en = kMultiBitBool4False,
              .ecc_en = kMultiBitBool4False,
              .high_endurance_en = kMultiBitBool4False,
          },
  };
  EXPECT_READ32(FLASH_CTRL_REGION_CFG_REGWEN_2_REG_OFFSET,
                {{FLASH_CTRL_REGION_CFG_REGWEN_2_REGION_2_BIT, 1}});

  EXPECT_READ32(
      FLASH_CTRL_MP_REGION_CFG_2_REG_OFFSET,
      {{FLASH_CTRL_MP_REGION_CFG_2_EN_2_OFFSET, kMultiBitBool4False}});

  EXPECT_WRITE32(
      FLASH_CTRL_MP_REGION_CFG_2_REG_OFFSET,
      {
          {FLASH_CTRL_MP_REGION_CFG_2_EN_2_OFFSET, kMultiBitBool4False},
          {FLASH_CTRL_MP_REGION_CFG_2_RD_EN_2_OFFSET, kMultiBitBool4False},
          {FLASH_CTRL_MP_REGION_CFG_2_PROG_EN_2_OFFSET, kMultiBitBool4True},
          {FLASH_CTRL_MP_REGION_CFG_2_ERASE_EN_2_OFFSET, kMultiBitBool4True},
          {FLASH_CTRL_MP_REGION_CFG_2_SCRAMBLE_EN_2_OFFSET,
           kMultiBitBool4False},
          {FLASH_CTRL_MP_REGION_CFG_2_ECC_EN_2_OFFSET, kMultiBitBool4False},
          {FLASH_CTRL_MP_REGION_CFG_2_HE_EN_2_OFFSET, kMultiBitBool4False},
      });

  EXPECT_WRITE32(FLASH_CTRL_MP_REGION_2_REG_OFFSET,
                 {
                     {FLASH_CTRL_MP_REGION_2_BASE_2_OFFSET, 0x48},
                     {FLASH_CTRL_MP_REGION_2_SIZE_2_OFFSET, 0x9a},
                 });

  EXPECT_DIF_OK(
      dif_flash_ctrl_set_data_region_properties(&dif_flash_ctrl_, 2, data_mp));

  // Enable the region
  EXPECT_READ32(FLASH_CTRL_REGION_CFG_REGWEN_3_REG_OFFSET,
                {{FLASH_CTRL_REGION_CFG_REGWEN_3_REGION_3_BIT, 1}});
  EXPECT_READ32(
      FLASH_CTRL_MP_REGION_CFG_3_REG_OFFSET,
      {
          {FLASH_CTRL_MP_REGION_CFG_3_EN_3_OFFSET, kMultiBitBool4False},
          {FLASH_CTRL_MP_REGION_CFG_3_RD_EN_3_OFFSET, kMultiBitBool4False},
          {FLASH_CTRL_MP_REGION_CFG_3_PROG_EN_3_OFFSET, kMultiBitBool4True},
          {FLASH_CTRL_MP_REGION_CFG_3_ERASE_EN_3_OFFSET, kMultiBitBool4True},
          {FLASH_CTRL_MP_REGION_CFG_3_SCRAMBLE_EN_3_OFFSET,
           kMultiBitBool4False},
          {FLASH_CTRL_MP_REGION_CFG_3_ECC_EN_3_OFFSET, kMultiBitBool4False},
          {FLASH_CTRL_MP_REGION_CFG_3_HE_EN_3_OFFSET, kMultiBitBool4False},
      });

  EXPECT_WRITE32(
      FLASH_CTRL_MP_REGION_CFG_3_REG_OFFSET,
      {
          {FLASH_CTRL_MP_REGION_CFG_3_EN_3_OFFSET, kMultiBitBool4True},
          {FLASH_CTRL_MP_REGION_CFG_3_RD_EN_3_OFFSET, kMultiBitBool4False},
          {FLASH_CTRL_MP_REGION_CFG_3_PROG_EN_3_OFFSET, kMultiBitBool4True},
          {FLASH_CTRL_MP_REGION_CFG_3_ERASE_EN_3_OFFSET, kMultiBitBool4True},
          {FLASH_CTRL_MP_REGION_CFG_3_SCRAMBLE_EN_3_OFFSET,
           kMultiBitBool4False},
          {FLASH_CTRL_MP_REGION_CFG_3_ECC_EN_3_OFFSET, kMultiBitBool4False},
          {FLASH_CTRL_MP_REGION_CFG_3_HE_EN_3_OFFSET, kMultiBitBool4False},
      });

  EXPECT_DIF_OK(dif_flash_ctrl_set_data_region_enablement(&dif_flash_ctrl_, 3,
                                                          kDifToggleEnabled));

  // Read out the region's configuration
  EXPECT_READ32(
      FLASH_CTRL_MP_REGION_CFG_3_REG_OFFSET,
      {
          {FLASH_CTRL_MP_REGION_CFG_3_RD_EN_3_OFFSET, kMultiBitBool4False},
          {FLASH_CTRL_MP_REGION_CFG_3_PROG_EN_3_OFFSET, kMultiBitBool4True},
          {FLASH_CTRL_MP_REGION_CFG_3_ERASE_EN_3_OFFSET, kMultiBitBool4True},
          {FLASH_CTRL_MP_REGION_CFG_3_SCRAMBLE_EN_3_OFFSET,
           kMultiBitBool4False},
          {FLASH_CTRL_MP_REGION_CFG_3_ECC_EN_3_OFFSET, kMultiBitBool4False},
          {FLASH_CTRL_MP_REGION_CFG_3_HE_EN_3_OFFSET, kMultiBitBool4False},
      });

  EXPECT_READ32(FLASH_CTRL_MP_REGION_3_REG_OFFSET,
                {
                    {FLASH_CTRL_MP_REGION_3_BASE_3_OFFSET, 0x48},
                    {FLASH_CTRL_MP_REGION_3_SIZE_3_OFFSET, 0x9a},
                });

  EXPECT_DIF_OK(
      dif_flash_ctrl_get_data_region_properties(&dif_flash_ctrl_, 3, &data_mp));
  EXPECT_EQ(data_mp.properties.rd_en, kMultiBitBool4False);
  EXPECT_EQ(data_mp.properties.prog_en, kMultiBitBool4True);
  EXPECT_EQ(data_mp.properties.erase_en, kMultiBitBool4True);
  EXPECT_EQ(data_mp.properties.scramble_en, kMultiBitBool4False);
  EXPECT_EQ(data_mp.properties.ecc_en, kMultiBitBool4False);
  EXPECT_EQ(data_mp.properties.high_endurance_en, kMultiBitBool4False);
  EXPECT_EQ(data_mp.base, 0x48);
  EXPECT_EQ(data_mp.size, 0x9a);

  // Lock the region
  EXPECT_READ32(FLASH_CTRL_REGION_CFG_REGWEN_3_REG_OFFSET,
                {{FLASH_CTRL_REGION_CFG_REGWEN_3_REGION_3_BIT, 1}});
  EXPECT_DIF_OK(
      dif_flash_ctrl_data_region_is_locked(&dif_flash_ctrl_, 3, &locked));
  EXPECT_FALSE(locked);

  EXPECT_READ32(FLASH_CTRL_REGION_CFG_REGWEN_3_REG_OFFSET,
                {{FLASH_CTRL_REGION_CFG_REGWEN_3_REGION_3_BIT, 1}});
  EXPECT_WRITE32(FLASH_CTRL_REGION_CFG_REGWEN_3_REG_OFFSET,
                 {{FLASH_CTRL_REGION_CFG_REGWEN_3_REGION_3_BIT, 0}});
  EXPECT_DIF_OK(
      dif_flash_ctrl_lock_data_region_properties(&dif_flash_ctrl_, 3));

  EXPECT_READ32(FLASH_CTRL_REGION_CFG_REGWEN_3_REG_OFFSET,
                {{FLASH_CTRL_REGION_CFG_REGWEN_3_REGION_3_BIT, 0}});
  EXPECT_DIF_OK(
      dif_flash_ctrl_data_region_is_locked(&dif_flash_ctrl_, 3, &locked));
  EXPECT_TRUE(locked);
  EXPECT_READ32(FLASH_CTRL_REGION_CFG_REGWEN_3_REG_OFFSET,
                {{FLASH_CTRL_REGION_CFG_REGWEN_3_REGION_3_BIT, 0}});
  EXPECT_EQ(
      dif_flash_ctrl_set_data_region_properties(&dif_flash_ctrl_, 3, data_mp),
      kDifLocked);
}

TEST_F(FlashCtrlTest, SimpleQueries) {
  dif_flash_ctrl_status_t status;
  EXPECT_READ32(FLASH_CTRL_STATUS_REG_OFFSET,
                {
                    {FLASH_CTRL_STATUS_RD_FULL_BIT, 0},
                    {FLASH_CTRL_STATUS_RD_EMPTY_BIT, 1},
                    {FLASH_CTRL_STATUS_PROG_FULL_BIT, 1},
                    {FLASH_CTRL_STATUS_PROG_EMPTY_BIT, 0},
                    {FLASH_CTRL_STATUS_INIT_WIP_BIT, 0},
                });
  EXPECT_DIF_OK(dif_flash_ctrl_get_status(&dif_flash_ctrl_, &status));
  EXPECT_EQ(status.read_fifo_full, 0);
  EXPECT_EQ(status.read_fifo_empty, 1);
  EXPECT_EQ(status.prog_fifo_full, 1);
  EXPECT_EQ(status.prog_fifo_empty, 0);
  EXPECT_EQ(status.controller_init_wip, 0);

  dif_flash_ctrl_error_t error_value;
  EXPECT_READ32(FLASH_CTRL_ERR_CODE_REG_OFFSET,
                {
                    {FLASH_CTRL_ERR_CODE_MP_ERR_BIT, 1},
                    {FLASH_CTRL_ERR_CODE_RD_ERR_BIT, 0},
                    {FLASH_CTRL_ERR_CODE_PROG_WIN_ERR_BIT, 0},
                    {FLASH_CTRL_ERR_CODE_PROG_TYPE_ERR_BIT, 1},
                    {FLASH_CTRL_ERR_CODE_UPDATE_ERR_BIT, 1},
                });
  EXPECT_READ32(FLASH_CTRL_ERR_ADDR_REG_OFFSET, 0x1effe0u);
  EXPECT_DIF_OK(dif_flash_ctrl_get_error_codes(&dif_flash_ctrl_, &error_value));
  EXPECT_EQ(error_value.codes.memory_properties_error, 1);
  EXPECT_EQ(error_value.codes.read_error, 0);
  EXPECT_EQ(error_value.codes.prog_window_error, 0);
  EXPECT_EQ(error_value.codes.prog_type_error, 1);
  EXPECT_EQ(error_value.codes.shadow_register_error, 1);
  EXPECT_EQ(error_value.address, 0x1effe0u);

  dif_toggle_t toggle;
  dif_flash_ctrl_info_region_t info_region = {
      .bank = 1,
      .partition_id = 0,
      .page = 3,
  };
  EXPECT_READ32(
      FLASH_CTRL_BANK1_INFO0_PAGE_CFG_3_REG_OFFSET,
      {
          {FLASH_CTRL_MP_REGION_CFG_0_EN_0_OFFSET, kMultiBitBool4True},
      });
  EXPECT_DIF_OK(dif_flash_ctrl_get_info_region_enablement(
      &dif_flash_ctrl_, info_region, &toggle));
  EXPECT_EQ(toggle, kDifToggleEnabled);

  dif_flash_ctrl_region_properties_t mp;
  EXPECT_READ32(
      FLASH_CTRL_DEFAULT_REGION_REG_OFFSET,
      {
          {FLASH_CTRL_DEFAULT_REGION_RD_EN_OFFSET, kMultiBitBool4True},
          {FLASH_CTRL_DEFAULT_REGION_PROG_EN_OFFSET, kMultiBitBool4True},
          {FLASH_CTRL_DEFAULT_REGION_ERASE_EN_OFFSET, kMultiBitBool4False},
          {FLASH_CTRL_DEFAULT_REGION_SCRAMBLE_EN_OFFSET, kMultiBitBool4False},
          {FLASH_CTRL_DEFAULT_REGION_ECC_EN_OFFSET, kMultiBitBool4True},
          {FLASH_CTRL_DEFAULT_REGION_HE_EN_OFFSET, kMultiBitBool4False},
      });
  EXPECT_DIF_OK(
      dif_flash_ctrl_get_default_region_properties(&dif_flash_ctrl_, &mp));
  EXPECT_EQ(mp.rd_en, kMultiBitBool4True);
  EXPECT_EQ(mp.prog_en, kMultiBitBool4True);
  EXPECT_EQ(mp.erase_en, kMultiBitBool4False);
  EXPECT_EQ(mp.scramble_en, kMultiBitBool4False);
  EXPECT_EQ(mp.ecc_en, kMultiBitBool4True);
  EXPECT_EQ(mp.high_endurance_en, kMultiBitBool4False);

  info_region.bank = 0;
  info_region.partition_id = 2;
  info_region.page = 1;
  EXPECT_READ32(FLASH_CTRL_BANK0_INFO2_PAGE_CFG_1_REG_OFFSET,
                {
                    {FLASH_CTRL_BANK0_INFO2_PAGE_CFG_1_RD_EN_1_OFFSET,
                     kMultiBitBool4True},
                    {FLASH_CTRL_BANK0_INFO2_PAGE_CFG_1_PROG_EN_1_OFFSET,
                     kMultiBitBool4False},
                    {FLASH_CTRL_BANK0_INFO2_PAGE_CFG_1_ERASE_EN_1_OFFSET,
                     kMultiBitBool4True},
                    {FLASH_CTRL_BANK0_INFO2_PAGE_CFG_1_SCRAMBLE_EN_1_OFFSET,
                     kMultiBitBool4False},
                    {FLASH_CTRL_BANK0_INFO2_PAGE_CFG_1_ECC_EN_1_OFFSET,
                     kMultiBitBool4True},
                    {FLASH_CTRL_BANK0_INFO2_PAGE_CFG_1_HE_EN_1_OFFSET,
                     kMultiBitBool4False},
                });
  EXPECT_DIF_OK(dif_flash_ctrl_get_info_region_properties(&dif_flash_ctrl_,
                                                          info_region, &mp));
  EXPECT_EQ(mp.rd_en, kMultiBitBool4True);
  EXPECT_EQ(mp.prog_en, kMultiBitBool4False);
  EXPECT_EQ(mp.erase_en, kMultiBitBool4True);
  EXPECT_EQ(mp.scramble_en, kMultiBitBool4False);
  EXPECT_EQ(mp.ecc_en, kMultiBitBool4True);
  EXPECT_EQ(mp.high_endurance_en, kMultiBitBool4False);

  bool locked;
  info_region.bank = 0;
  info_region.partition_id = 0;
  info_region.page = 2;
  EXPECT_READ32(FLASH_CTRL_BANK0_INFO0_REGWEN_2_REG_OFFSET,
                {{FLASH_CTRL_BANK0_INFO0_REGWEN_2_REGION_2_BIT, 1}});
  EXPECT_DIF_OK(dif_flash_ctrl_info_region_is_locked(&dif_flash_ctrl_,
                                                     info_region, &locked));
  EXPECT_FALSE(locked);

  EXPECT_READ32(FLASH_CTRL_MP_BANK_CFG_SHADOWED_REG_OFFSET,
                {
                    {FLASH_CTRL_MP_BANK_CFG_SHADOWED_ERASE_EN_0_BIT, 0},
                    {FLASH_CTRL_MP_BANK_CFG_SHADOWED_ERASE_EN_1_BIT, 1},
                });
  EXPECT_DIF_OK(
      dif_flash_ctrl_get_bank_erase_enablement(&dif_flash_ctrl_, 1, &toggle));
  EXPECT_EQ(toggle, kDifToggleEnabled);

  EXPECT_READ32(FLASH_CTRL_BANK_CFG_REGWEN_REG_OFFSET,
                {{FLASH_CTRL_BANK_CFG_REGWEN_BANK_BIT, 1}});
  EXPECT_DIF_OK(
      dif_flash_ctrl_bank_configuration_is_locked(&dif_flash_ctrl_, &locked));
  EXPECT_FALSE(locked);

  uint32_t prog_level, read_level;
  EXPECT_READ32(FLASH_CTRL_FIFO_LVL_REG_OFFSET,
                {
                    {FLASH_CTRL_FIFO_LVL_PROG_OFFSET, 9},
                    {FLASH_CTRL_FIFO_LVL_RD_OFFSET, 13},
                });
  EXPECT_DIF_OK(dif_flash_ctrl_get_fifo_watermarks(&dif_flash_ctrl_,
                                                   &prog_level, &read_level));
  EXPECT_EQ(prog_level, 9);
  EXPECT_EQ(read_level, 13);

  dif_flash_ctrl_faults_t faults;
  EXPECT_READ32(FLASH_CTRL_FAULT_STATUS_REG_OFFSET,
                {
                    {FLASH_CTRL_FAULT_STATUS_MP_ERR_BIT, 1},
                    {FLASH_CTRL_FAULT_STATUS_RD_ERR_BIT, 0},
                    {FLASH_CTRL_FAULT_STATUS_PROG_WIN_ERR_BIT, 1},
                    {FLASH_CTRL_FAULT_STATUS_PROG_TYPE_ERR_BIT, 0},
                });
  EXPECT_READ32(FLASH_CTRL_STD_FAULT_STATUS_REG_OFFSET,
                {
                    {FLASH_CTRL_STD_FAULT_STATUS_REG_INTG_ERR_BIT, 0},
                    {FLASH_CTRL_STD_FAULT_STATUS_PROG_INTG_ERR_BIT, 1},
                    {FLASH_CTRL_STD_FAULT_STATUS_LCMGR_ERR_BIT, 0},
                    {FLASH_CTRL_STD_FAULT_STATUS_STORAGE_ERR_BIT, 1},
                });
  EXPECT_DIF_OK(dif_flash_ctrl_get_faults(&dif_flash_ctrl_, &faults));
  EXPECT_EQ(faults.memory_properties_error, 1);
  EXPECT_EQ(faults.read_error, 0);
  EXPECT_EQ(faults.prog_window_error, 1);
  EXPECT_EQ(faults.prog_type_error, 0);
  EXPECT_EQ(faults.register_integrity_error, 0);
  EXPECT_EQ(faults.phy_integrity_error, 1);
  EXPECT_EQ(faults.lifecycle_manager_error, 0);
  EXPECT_EQ(faults.shadow_storage_error, 1);

  dif_flash_ctrl_ecc_errors_t ecc_errors;
  EXPECT_READ32(
      FLASH_CTRL_ECC_SINGLE_ERR_CNT_REG_OFFSET,
      {
          {FLASH_CTRL_ECC_SINGLE_ERR_CNT_ECC_SINGLE_ERR_CNT_0_OFFSET, 7},
          {FLASH_CTRL_ECC_SINGLE_ERR_CNT_ECC_SINGLE_ERR_CNT_1_OFFSET, 11},
      });
  EXPECT_READ32(FLASH_CTRL_ECC_SINGLE_ERR_ADDR_1_REG_OFFSET, 0x16487590u);
  EXPECT_DIF_OK(
      dif_flash_ctrl_get_ecc_errors(&dif_flash_ctrl_, 1, &ecc_errors));
  EXPECT_EQ(ecc_errors.single_bit_error_count, 11);
  EXPECT_EQ(ecc_errors.last_error_address, 0x16487590u);

  dif_flash_ctrl_phy_status_t phy_status;
  EXPECT_READ32(FLASH_CTRL_PHY_STATUS_REG_OFFSET,
                {
                    {FLASH_CTRL_PHY_STATUS_INIT_WIP_BIT, 0},
                    {FLASH_CTRL_PHY_STATUS_PROG_NORMAL_AVAIL_BIT, 1},
                    {FLASH_CTRL_PHY_STATUS_PROG_REPAIR_AVAIL_BIT, 0},
                });
  EXPECT_DIF_OK(dif_flash_ctrl_get_phy_status(&dif_flash_ctrl_, &phy_status));
  EXPECT_EQ(phy_status.phy_init_wip, 0);
  EXPECT_EQ(phy_status.prog_normal_available, 1);
  EXPECT_EQ(phy_status.prog_repair_available, 0);

  uint32_t scratch;
  EXPECT_READ32(FLASH_CTRL_SCRATCH_REG_OFFSET, 0x89abcdefu);
  EXPECT_DIF_OK(dif_flash_ctrl_get_scratch(&dif_flash_ctrl_, &scratch));
  EXPECT_EQ(scratch, 0x89abcdefu);
}

}  // namespace
}  // namespace dif_flash_ctrl_unittest
