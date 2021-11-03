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

TEST_F(StatusCheckTest, DefaultStatus) {
  EXPECT_ABS_READ32(base_ + FLASH_CTRL_STATUS_REG_OFFSET,
                    {
                        {FLASH_CTRL_STATUS_RD_FULL_BIT, false},
                        {FLASH_CTRL_STATUS_RD_EMPTY_BIT, false},
                        {FLASH_CTRL_STATUS_INIT_WIP_BIT, false},
                    });

  flash_ctrl_status_t status;
  flash_ctrl_status_get(&status);

  EXPECT_EQ(status.init_wip, false);
  EXPECT_EQ(status.rd_empty, false);
  EXPECT_EQ(status.rd_full, false);
}

TEST_F(StatusCheckTest, AllSetStatus) {
  EXPECT_ABS_READ32(base_ + FLASH_CTRL_STATUS_REG_OFFSET,
                    {
                        {FLASH_CTRL_STATUS_RD_FULL_BIT, true},
                        {FLASH_CTRL_STATUS_RD_EMPTY_BIT, true},
                        {FLASH_CTRL_STATUS_INIT_WIP_BIT, true},
                    });

  flash_ctrl_status_t status;
  flash_ctrl_status_get(&status);

  EXPECT_EQ(status.init_wip, true);
  EXPECT_EQ(status.rd_empty, true);
  EXPECT_EQ(status.rd_full, true);
}

class TransferTest : public FlashCtrlTest {
 protected:
  const std::vector<uint32_t> words_ = {0x12345678, 0x90ABCDEF, 0x0F1E2D3C,
                                        0x4B5A6978};
  void ExpectCheckBusy(bool busy) {
    EXPECT_ABS_READ32(base_ + FLASH_CTRL_CTRL_REGWEN_REG_OFFSET,
                      {{FLASH_CTRL_CTRL_REGWEN_EN_BIT, !busy}});
  }

  void ExpectWaitForDone(bool done, bool error) {
    EXPECT_ABS_READ32(base_ + FLASH_CTRL_OP_STATUS_REG_OFFSET,
                      {{FLASH_CTRL_OP_STATUS_DONE_BIT, done},
                       {FLASH_CTRL_OP_STATUS_ERR_BIT, error}});
    if (done) {
      EXPECT_ABS_WRITE32(base_ + FLASH_CTRL_OP_STATUS_REG_OFFSET, 0u);
    }
  }

  void ExpectTransferStart(uint8_t part_sel, uint8_t info_sel,
                           uint8_t erase_sel, uint32_t op, uint32_t addr,
                           uint32_t word_count) {
    ExpectCheckBusy(false);
    EXPECT_ABS_WRITE32(base_ + FLASH_CTRL_ADDR_REG_OFFSET, addr);
    EXPECT_ABS_WRITE32(base_ + FLASH_CTRL_CONTROL_REG_OFFSET,
                       {
                           {FLASH_CTRL_CONTROL_OP_OFFSET, op},
                           {FLASH_CTRL_CONTROL_PARTITION_SEL_BIT, part_sel},
                           {FLASH_CTRL_CONTROL_INFO_SEL_OFFSET, info_sel},
                           {FLASH_CTRL_CONTROL_ERASE_SEL_BIT, erase_sel},
                           {FLASH_CTRL_CONTROL_NUM_OFFSET, word_count - 1},
                           {FLASH_CTRL_CONTROL_START_BIT, 1},
                       });
  }

  void ExpectReadData(const std::vector<uint32_t> &data) {
    for (auto val : data) {
      EXPECT_ABS_READ32(base_ + FLASH_CTRL_RD_FIFO_REG_OFFSET, val);
    }
  }

  void ExpectProgData(const std::vector<uint32_t> &data) {
    for (auto val : data) {
      EXPECT_ABS_WRITE32(base_ + FLASH_CTRL_PROG_FIFO_REG_OFFSET, val);
    }
  }
};

TEST_F(TransferTest, ReadBusy) {
  ExpectCheckBusy(true);
  EXPECT_EQ(flash_ctrl_read(0, 0, kFlashCtrlPartitionData, NULL),
            kErrorFlashCtrlBusy);
}

TEST_F(TransferTest, ProgBusy) {
  ExpectCheckBusy(true);
  EXPECT_EQ(flash_ctrl_prog(0, 4, kFlashCtrlPartitionData, NULL),
            kErrorFlashCtrlBusy);
}

TEST_F(TransferTest, EraseBusy) {
  ExpectCheckBusy(true);
  EXPECT_EQ(
      flash_ctrl_erase(0, kFlashCtrlPartitionData, kFlashCtrlEraseTypePage),
      kErrorFlashCtrlBusy);
}

TEST_F(TransferTest, ReadDataOk) {
  ExpectTransferStart(0, 0, 0, FLASH_CTRL_CONTROL_OP_VALUE_READ, 0x01234567,
                      words_.size());
  ExpectReadData(words_);
  ExpectWaitForDone(true, false);
  std::vector<uint32_t> words_out(words_.size());
  EXPECT_EQ(flash_ctrl_read(0x01234567, words_.size(), kFlashCtrlPartitionData,
                            &words_out.front()),
            kErrorOk);
  EXPECT_EQ(words_out, words_);
}

TEST_F(TransferTest, ProgDataOk) {
  ExpectTransferStart(0, 0, 0, FLASH_CTRL_CONTROL_OP_VALUE_PROG, 0x01234567,
                      words_.size());
  ExpectProgData(words_);
  ExpectWaitForDone(true, false);
  EXPECT_EQ(flash_ctrl_prog(0x01234567, words_.size(), kFlashCtrlPartitionData,
                            &words_.front()),
            kErrorOk);
}

TEST_F(TransferTest, EraseDataPageOk) {
  ExpectTransferStart(0, 0, 0, FLASH_CTRL_CONTROL_OP_VALUE_ERASE, 0x01234567,
                      1);
  ExpectWaitForDone(true, false);
  EXPECT_EQ(flash_ctrl_erase(0x01234567, kFlashCtrlPartitionData,
                             kFlashCtrlEraseTypePage),
            kErrorOk);
}

TEST_F(TransferTest, ProgAcrossWindows) {
  static const uint32_t kWinSize = FLASH_CTRL_PARAM_REG_BUS_PGM_RES_BYTES;
  static const uint32_t kManyWordsSize = 2 * kWinSize / sizeof(uint32_t);

  std::array<uint32_t, kManyWordsSize> many_words;
  for (uint32_t i = 0; i < many_words.size(); ++i) {
    many_words[i] = i;
  }

  auto iter = many_words.begin();
  size_t half_step = kWinSize / sizeof(uint32_t) / 2;

  // Program address range [0x20, 0x40)
  ExpectTransferStart(0, 0, 0, FLASH_CTRL_CONTROL_OP_VALUE_PROG, kWinSize / 2,
                      half_step);
  ExpectProgData(std::vector<uint32_t>(iter, iter + half_step));
  ExpectWaitForDone(true, false);
  iter += half_step;

  // Program address range [0x40, 0x80)
  ExpectTransferStart(0, 0, 0, FLASH_CTRL_CONTROL_OP_VALUE_PROG, kWinSize,
                      2 * half_step);
  ExpectProgData(std::vector<uint32_t>(iter, iter + 2 * half_step));
  ExpectWaitForDone(true, false);
  iter += 2 * half_step;

  // Programm address range [0x80, 0xA0)
  ExpectTransferStart(0, 0, 0, FLASH_CTRL_CONTROL_OP_VALUE_PROG, 2 * kWinSize,
                      half_step);
  ExpectProgData(std::vector<uint32_t>(iter, iter + half_step));
  ExpectWaitForDone(true, false);

  EXPECT_EQ(iter + half_step, many_words.end());

  EXPECT_EQ(flash_ctrl_prog(kWinSize / 2, many_words.size(),
                            kFlashCtrlPartitionData, &many_words.front()),
            kErrorOk);
}

TEST_F(TransferTest, TransferInternalError) {
  ExpectTransferStart(0, 0, 0, FLASH_CTRL_CONTROL_OP_VALUE_READ, 0x01234567,
                      words_.size());
  ExpectReadData(words_);
  ExpectWaitForDone(true, true);
  std::vector<uint32_t> words_out(words_.size());
  EXPECT_EQ(flash_ctrl_read(0x01234567, words_.size(), kFlashCtrlPartitionData,
                            &words_out.front()),
            kErrorFlashCtrlInternal);
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
