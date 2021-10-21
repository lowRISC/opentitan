// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/base/testing/mock_mmio_test_utils.h"
#include "sw/device/silicon_creator/lib/base/mock_abs_mmio.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "flash_ctrl_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

namespace flash_ctrl_unittest {
namespace {
using ::testing::ElementsAre;

class FlashCtrlTest : public mask_rom_test::MaskRomTest {
 protected:
  uint32_t base_ = TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR;
  mask_rom_test::MockAbsMmio mmio_;
};

class InitTest : public FlashCtrlTest {};

TEST_F(InitTest, Initialize) {
  EXPECT_ABS_WRITE32(base_ + FLASH_CTRL_INIT_REG_OFFSET,
                     {{FLASH_CTRL_INIT_VAL_BIT, true}});

  flash_ctrl_init();
}

class StatusCheckTest : public FlashCtrlTest {};

TEST_F(StatusCheckTest, InvalidArgument) {
  EXPECT_EQ(flash_ctrl_status_get(NULL), kErrorFlashCtrlInvalidArgument);
}

TEST_F(StatusCheckTest, DefaultStatus) {
  EXPECT_ABS_READ32(base_ + FLASH_CTRL_OP_STATUS_REG_OFFSET,
                    {
                        {FLASH_CTRL_OP_STATUS_DONE_BIT, false},
                        {FLASH_CTRL_OP_STATUS_ERR_BIT, false},
                    });
  EXPECT_ABS_READ32(base_ + FLASH_CTRL_STATUS_REG_OFFSET,
                    {
                        {FLASH_CTRL_STATUS_RD_FULL_BIT, false},
                        {FLASH_CTRL_STATUS_RD_EMPTY_BIT, false},
                        {FLASH_CTRL_STATUS_INIT_WIP_BIT, false},
                    });

  flash_ctrl_status_t status;
  EXPECT_EQ(flash_ctrl_status_get(&status), kErrorOk);

  EXPECT_EQ(status.done, false);
  EXPECT_EQ(status.err, false);
  EXPECT_EQ(status.init_wip, false);
  EXPECT_EQ(status.rd_empty, false);
  EXPECT_EQ(status.rd_full, false);
}

TEST_F(StatusCheckTest, AllSetStatus) {
  EXPECT_ABS_READ32(base_ + FLASH_CTRL_OP_STATUS_REG_OFFSET,
                    {
                        {FLASH_CTRL_OP_STATUS_DONE_BIT, true},
                        {FLASH_CTRL_OP_STATUS_ERR_BIT, true},
                    });
  EXPECT_ABS_READ32(base_ + FLASH_CTRL_STATUS_REG_OFFSET,
                    {
                        {FLASH_CTRL_STATUS_RD_FULL_BIT, true},
                        {FLASH_CTRL_STATUS_RD_EMPTY_BIT, true},
                        {FLASH_CTRL_STATUS_INIT_WIP_BIT, true},
                    });

  flash_ctrl_status_t status;
  EXPECT_EQ(flash_ctrl_status_get(&status), kErrorOk);

  EXPECT_EQ(status.done, true);
  EXPECT_EQ(status.err, true);
  EXPECT_EQ(status.init_wip, true);
  EXPECT_EQ(status.rd_empty, true);
  EXPECT_EQ(status.rd_full, true);
}

class ReadStartTest : public FlashCtrlTest {
 protected:
  void ExpectCheckBusy(bool busy) {
    EXPECT_ABS_READ32(base_ + FLASH_CTRL_CTRL_REGWEN_REG_OFFSET,
                      {{FLASH_CTRL_CTRL_REGWEN_EN_BIT, !busy}});
  }
  void ExpectReadStart(uint8_t part_sel, uint8_t info_sel) {
    EXPECT_ABS_WRITE32(base_ + FLASH_CTRL_ADDR_REG_OFFSET, 0x01234567);
    EXPECT_ABS_WRITE32(
        base_ + FLASH_CTRL_CONTROL_REG_OFFSET,
        {
            {FLASH_CTRL_CONTROL_OP_OFFSET, FLASH_CTRL_CONTROL_OP_VALUE_READ},
            {FLASH_CTRL_CONTROL_PARTITION_SEL_BIT, part_sel},
            {FLASH_CTRL_CONTROL_INFO_SEL_OFFSET, info_sel},
            {FLASH_CTRL_CONTROL_NUM_OFFSET, 42},
            {FLASH_CTRL_CONTROL_START_BIT, 1},
        });
  }
};

TEST_F(ReadStartTest, Busy) {
  ExpectCheckBusy(true);
  EXPECT_EQ(flash_ctrl_read_start(0, 0, kFlashCtrlRegionData),
            kErrorFlashCtrlBusy);
}

TEST_F(ReadStartTest, ReadData) {
  ExpectCheckBusy(false);
  ExpectReadStart(0, 0);
  EXPECT_EQ(flash_ctrl_read_start(0x01234567, 42, kFlashCtrlRegionData),
            kErrorOk);
}

TEST_F(ReadStartTest, ReadInfo) {
  ExpectCheckBusy(false);
  ExpectReadStart(1, 2);
  EXPECT_EQ(flash_ctrl_read_start(0x01234567, 42, kFlashCtrlRegionInfo2),
            kErrorOk);
}

class ReadTest : public FlashCtrlTest {
 protected:
  const std::vector<uint32_t> words_ = {0x12345678, 0x90ABCDEF, 0x0F1E2D3C,
                                        0x4B5A6978};
  void ExpectReadData(const std::vector<uint32_t> &data) {
    for (auto val : data) {
      EXPECT_ABS_READ32(base_ + FLASH_CTRL_RD_FIFO_REG_OFFSET, val);
    }
  }
};

TEST_F(ReadTest, ReadAll) {
  ExpectReadData(words_);
  std::vector<uint32_t> words_out(words_.size());
  EXPECT_EQ(flash_ctrl_fifo_read(words_.size(), &words_out.front()),
            words_.size());
  EXPECT_EQ(words_out, words_);
}

class ExecTest : public FlashCtrlTest {};

TEST_F(ExecTest, Enable) {
  EXPECT_ABS_WRITE32(base_ + FLASH_CTRL_EXEC_REG_OFFSET, kMultiBitBool4True);
  flash_ctrl_exec_set(kFlashCtrlExecEnable);
}

TEST_F(ExecTest, Disable) {
  // Note: any value that is not `0xa` will disable execution.
  EXPECT_ABS_WRITE32(base_ + FLASH_CTRL_EXEC_REG_OFFSET, kMultiBitBool4False);
  flash_ctrl_exec_set(kFlashCtrlExecDisable);
}

}  // namespace
}  // namespace flash_ctrl_unittest
