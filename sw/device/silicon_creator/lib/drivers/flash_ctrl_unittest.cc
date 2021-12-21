// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/base/testing/mock_mmio_test_utils.h"
#include "sw/device/silicon_creator/lib/base/mock_abs_mmio.h"
#include "sw/device/silicon_creator/lib/base/mock_sec_mmio.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "flash_ctrl_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

namespace flash_ctrl_unittest {
namespace {
using ::testing::Each;
using ::testing::SizeIs;

/**
 * A struct that holds bank, page, and config register information for an
 * information page.
 */
struct InfoPage {
  uint32_t bank;
  uint32_t page;
  uint32_t cfg_offset;
  uint32_t cfg_wen_offset;
};

/**
 * Returns a map from `flash_ctrl_info_page_t` to `InfoPage` to be used in
 * tests.
 */
const std::map<flash_ctrl_info_page_t, InfoPage> &InfoPages() {
#define INFO_PAGE_MAP_INIT(name_, bank_, page_)                                    \
  {                                                                                \
    name_,                                                                         \
        {                                                                          \
            bank_,                                                                 \
            page_,                                                                 \
            FLASH_CTRL_BANK##bank_##_INFO0_PAGE_CFG_SHADOWED_##page_##_REG_OFFSET, \
            FLASH_CTRL_BANK##bank_##_INFO0_REGWEN_##page_##_REG_OFFSET,            \
        },                                                                         \
  }

  static const std::map<flash_ctrl_info_page_t, InfoPage> *const kInfoPages =
      new std::map<flash_ctrl_info_page_t, InfoPage>{
          FLASH_CTRL_INFO_PAGES_DEFINE(INFO_PAGE_MAP_INIT)};
  return *kInfoPages;
}

class FlashCtrlTest : public mask_rom_test::MaskRomTest {
 protected:
  uint32_t base_ = TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR;
  mask_rom_test::MockAbsMmio mmio_;
  mask_rom_test::MockSecMmio sec_mmio_;
};

class InfoPagesTest : public FlashCtrlTest {};
TEST_F(InfoPagesTest, NumberOfPages) { EXPECT_THAT(InfoPages(), SizeIs(20)); }

TEST_F(InfoPagesTest, PagesPerBank) {
  std::array<uint32_t, 2> pages_per_bank = {0, 0};
  for (const auto &it : InfoPages()) {
    const uint32_t bank = it.second.bank;
    EXPECT_EQ(bank, static_cast<uint32_t>(bitfield_bit32_read(
                        it.first, FLASH_CTRL_INFO_PAGE_BIT_BANK)));
    EXPECT_LE(bank, 1);
    ++pages_per_bank[bank];
  }

  EXPECT_THAT(pages_per_bank, Each(10));
}

TEST_F(InfoPagesTest, AllType0) {
  for (const auto &it : InfoPages()) {
    const flash_ctrl_partition_t partition =
        static_cast<flash_ctrl_partition_t>(bitfield_field32_read(
            it.first, FLASH_CTRL_INFO_PAGE_FIELD_PARTITION));
    EXPECT_EQ(partition, kFlashCtrlPartitionInfo0);
  }
}

TEST_F(InfoPagesTest, PageIndices) {
  for (const auto &it : InfoPages()) {
    const uint32_t page = it.second.page;

    EXPECT_EQ(page,
              bitfield_field32_read(it.first, FLASH_CTRL_INFO_PAGE_FIELD_PAGE));
    EXPECT_LE(page, 9);
  }
}

class InitTest : public FlashCtrlTest {};

TEST_F(InitTest, Initialize) {
  EXPECT_ABS_WRITE32(base_ + FLASH_CTRL_INIT_REG_OFFSET,
                     {{FLASH_CTRL_INIT_VAL_BIT, true}});
  auto info_page = InfoPages().at(kFlashCtrlInfoPageCreatorSecret);
  EXPECT_SEC_WRITE32_SHADOWED(base_ + info_page.cfg_offset, 0);
  EXPECT_SEC_WRITE32(base_ + info_page.cfg_wen_offset, 0);
  EXPECT_SEC_WRITE_INCREMENT(2);

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

TEST_F(TransferTest, ReadDataOk) {
  ExpectTransferStart(0, 0, 0, FLASH_CTRL_CONTROL_OP_VALUE_READ, 0x01234567,
                      words_.size());
  ExpectReadData(words_);
  ExpectWaitForDone(true, false);
  std::vector<uint32_t> words_out(words_.size());
  EXPECT_EQ(flash_ctrl_data_read(0x01234567, words_.size(), &words_out.front()),
            kErrorOk);
  EXPECT_EQ(words_out, words_);
}

TEST_F(TransferTest, ProgDataOk) {
  ExpectTransferStart(0, 0, 0, FLASH_CTRL_CONTROL_OP_VALUE_PROG, 0x01234567,
                      words_.size());
  ExpectProgData(words_);
  ExpectWaitForDone(true, false);
  EXPECT_EQ(flash_ctrl_data_write(0x01234567, words_.size(), &words_.front()),
            kErrorOk);
}

TEST_F(TransferTest, EraseDataPageOk) {
  ExpectTransferStart(0, 0, 0, FLASH_CTRL_CONTROL_OP_VALUE_ERASE, 0x01234567,
                      1);
  ExpectWaitForDone(true, false);
  EXPECT_EQ(flash_ctrl_data_erase(0x01234567, kFlashCtrlEraseTypePage),
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

  EXPECT_EQ(flash_ctrl_data_write(kWinSize / 2, many_words.size(),
                                  &many_words.front()),
            kErrorOk);
}

TEST_F(TransferTest, TransferInternalError) {
  ExpectTransferStart(0, 0, 0, FLASH_CTRL_CONTROL_OP_VALUE_READ, 0x01234567,
                      words_.size());
  ExpectReadData(words_);
  ExpectWaitForDone(true, true);
  std::vector<uint32_t> words_out(words_.size());
  EXPECT_EQ(flash_ctrl_data_read(0x01234567, words_.size(), &words_out.front()),
            kErrorFlashCtrlDataRead);
}

class ExecTest : public FlashCtrlTest {};

TEST_F(ExecTest, Enable) {
  EXPECT_SEC_WRITE32(base_ + FLASH_CTRL_EXEC_REG_OFFSET, kMultiBitBool4True);
  EXPECT_SEC_WRITE_INCREMENT(1);
  flash_ctrl_exec_set(kFlashCtrlExecEnable);
}

TEST_F(ExecTest, Disable) {
  // Note: any value that is not `0xa` will disable execution.
  EXPECT_SEC_WRITE32(base_ + FLASH_CTRL_EXEC_REG_OFFSET, kMultiBitBool4False);
  EXPECT_SEC_WRITE_INCREMENT(1);
  flash_ctrl_exec_set(kFlashCtrlExecDisable);
}

struct InfoMpSetCase {
  /**
   * Access permissions to set.
   */
  flash_ctrl_perms_t perms;
  /**
   * Expected value to be read from the config register.
   */
  uint32_t read_val;
  /**
   * Expected value to be written to the config register.
   */
  uint32_t write_val;
};

class FlashCtrlInfoMpSetTest
    : public FlashCtrlTest,
      public testing::WithParamInterface<InfoMpSetCase> {};

TEST_P(FlashCtrlInfoMpSetTest, InfoMpSet) {
  for (const auto &it : InfoPages()) {
    EXPECT_SEC_READ32(base_ + it.second.cfg_offset, GetParam().read_val);
    EXPECT_SEC_WRITE32_SHADOWED(base_ + it.second.cfg_offset,
                                GetParam().write_val);
    EXPECT_SEC_WRITE_INCREMENT(1);

    flash_ctrl_info_perms_set(it.first, GetParam().perms);
  }
}

INSTANTIATE_TEST_SUITE_P(AllCases, FlashCtrlInfoMpSetTest,
                         testing::Values(
                             // Read.
                             InfoMpSetCase{
                                 .perms = {.read = kHardenedBoolTrue,
                                           .write = kHardenedBoolFalse,
                                           .erase = kHardenedBoolFalse},
                                 .read_val = 0x0,
                                 .write_val = 0x3,
                             },
                             InfoMpSetCase{
                                 .perms = {.read = kHardenedBoolTrue,
                                           .write = kHardenedBoolFalse,
                                           .erase = kHardenedBoolFalse},
                                 .read_val = 0x7f,
                                 .write_val = 0x73,
                             },
                             // Write.
                             InfoMpSetCase{
                                 .perms = {.read = kHardenedBoolFalse,
                                           .write = kHardenedBoolTrue,
                                           .erase = kHardenedBoolFalse},
                                 .read_val = 0x0,
                                 .write_val = 0x5,
                             },
                             InfoMpSetCase{
                                 .perms = {.read = kHardenedBoolFalse,
                                           .write = kHardenedBoolTrue,
                                           .erase = kHardenedBoolFalse},
                                 .read_val = 0x7f,
                                 .write_val = 0x75,
                             },
                             // Erase.
                             InfoMpSetCase{
                                 .perms = {.read = kHardenedBoolFalse,
                                           .write = kHardenedBoolFalse,
                                           .erase = kHardenedBoolTrue},
                                 .read_val = 0x0,
                                 .write_val = 0x9,
                             },
                             InfoMpSetCase{
                                 .perms = {.read = kHardenedBoolFalse,
                                           .write = kHardenedBoolFalse,
                                           .erase = kHardenedBoolTrue},
                                 .read_val = 0x7f,
                                 .write_val = 0x79,
                             },
                             // Write and erase.
                             InfoMpSetCase{
                                 .perms = {.read = kHardenedBoolFalse,
                                           .write = kHardenedBoolTrue,
                                           .erase = kHardenedBoolTrue},
                                 .read_val = 0x0,
                                 .write_val = 0xd,
                             },
                             InfoMpSetCase{
                                 .perms = {.read = kHardenedBoolFalse,
                                           .write = kHardenedBoolTrue,
                                           .erase = kHardenedBoolTrue},
                                 .read_val = 0x7f,
                                 .write_val = 0x7d,
                             }));

TEST_F(FlashCtrlTest, CreatorInfoLockdown) {
  std::array<flash_ctrl_info_page_t, 6> no_owner_access = {
      kFlashCtrlInfoPageOwnerSecret, kFlashCtrlInfoPageWaferAuthSecret,
      kFlashCtrlInfoPageBootData0,   kFlashCtrlInfoPageBootData1,
      kFlashCtrlInfoPageOwnerSlot0,  kFlashCtrlInfoPageOwnerSlot1,
  };
  for (auto page : no_owner_access) {
    auto info_page = InfoPages().at(page);
    EXPECT_SEC_WRITE32_SHADOWED(base_ + info_page.cfg_offset, 0);
    EXPECT_SEC_WRITE32(base_ + info_page.cfg_wen_offset, 0);
  }
  EXPECT_SEC_WRITE_INCREMENT(2 * no_owner_access.size());

  flash_ctrl_creator_info_pages_lockdown();
}

}  // namespace
}  // namespace flash_ctrl_unittest
