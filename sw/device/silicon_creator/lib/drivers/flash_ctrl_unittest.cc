// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"

#include <array>

#include "gtest/gtest.h"
#include "sw/device/lib/base/mock_abs_mmio.h"
#include "sw/device/lib/base/mock_mmio_test_utils.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/silicon_creator/lib/base/mock_sec_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/mock_otp.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

#include "flash_ctrl_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"

namespace flash_ctrl_unittest {
namespace {
using ::testing::Each;
using ::testing::Return;
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
#define INFO_PAGE_MAP_INIT(name_, value_, bank_, page_)                 \
  {                                                                     \
      name_,                                                            \
      {                                                                 \
          bank_,                                                        \
          page_,                                                        \
          FLASH_CTRL_BANK##bank_##_INFO0_PAGE_CFG_##page_##_REG_OFFSET, \
          FLASH_CTRL_BANK##bank_##_INFO0_REGWEN_##page_##_REG_OFFSET,   \
      },                                                                \
  },

  static const std::map<flash_ctrl_info_page_t, InfoPage> *const kInfoPages =
      new std::map<flash_ctrl_info_page_t, InfoPage>{
          FLASH_CTRL_INFO_PAGES_DEFINE(INFO_PAGE_MAP_INIT)};
  return *kInfoPages;
}

class FlashCtrlTest : public rom_test::RomTest {
 protected:
  uint32_t base_ = TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR;
  rom_test::MockAbsMmio mmio_;
  rom_test::MockSecMmio sec_mmio_;
  rom_test::MockOtp otp_;
};

class InfoPagesTest : public FlashCtrlTest {};
TEST_F(InfoPagesTest, NumberOfPages) { EXPECT_THAT(InfoPages(), SizeIs(20)); }

TEST_F(InfoPagesTest, PagesPerBank) {
  std::array<uint32_t, 2> pages_per_bank = {0, 0};
  for (const auto &it : InfoPages()) {
    const uint32_t bank = it.second.bank;
    EXPECT_LE(bank, 1);
    ++pages_per_bank[bank];
  }

  EXPECT_THAT(pages_per_bank, Each(10));
}

TEST_F(InfoPagesTest, PageIndices) {
  for (const auto &it : InfoPages()) {
    const uint32_t page = it.second.page;
    EXPECT_LE(page, 9);
  }
}

struct InitCase {
  /**
   * Configuration settings to be read from OTP.
   */
  flash_ctrl_cfg_t cfg;
  /**
   * Expected value to be written to the info config register.
   */
  uint32_t info_write_val;
  /**
   * Expected value to be written to the data config register.
   */
  uint32_t data_write_val;
};

class InitTest : public FlashCtrlTest,
                 public testing::WithParamInterface<InitCase> {};

uint32_t CfgToOtp(flash_ctrl_cfg_t cfg) {
  uint32_t val = bitfield_field32_write(0, FLASH_CTRL_OTP_FIELD_SCRAMBLING,
                                        cfg.scrambling);
  val = bitfield_field32_write(val, FLASH_CTRL_OTP_FIELD_ECC, cfg.ecc);
  val = bitfield_field32_write(val, FLASH_CTRL_OTP_FIELD_HE, cfg.he);
  return val;
}

TEST_P(InitTest, Initialize) {
  EXPECT_CALL(
      otp_,
      read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_FLASH_HW_INFO_CFG_OVERRIDE_OFFSET))
      .WillOnce(Return(0));

  EXPECT_ABS_WRITE32(base_ + FLASH_CTRL_INIT_REG_OFFSET,
                     {{FLASH_CTRL_INIT_VAL_BIT, true}});

  EXPECT_CALL(
      otp_, read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_FLASH_DATA_DEFAULT_CFG_OFFSET))
      .WillOnce(Return(CfgToOtp(GetParam().cfg)));
  EXPECT_SEC_READ32(base_ + FLASH_CTRL_DEFAULT_REGION_REG_OFFSET,
                    FLASH_CTRL_DEFAULT_REGION_REG_RESVAL);
  EXPECT_SEC_WRITE32(base_ + FLASH_CTRL_DEFAULT_REGION_REG_OFFSET,
                     GetParam().data_write_val);

  EXPECT_CALL(
      otp_,
      read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_FLASH_INFO_BOOT_DATA_CFG_OFFSET))
      .WillOnce(Return(CfgToOtp(GetParam().cfg)));
  auto info_page = InfoPages().at(kFlashCtrlInfoPageBootData0);
  EXPECT_SEC_READ32(base_ + info_page.cfg_offset,
                    FLASH_CTRL_BANK0_INFO0_PAGE_CFG_0_REG_RESVAL);
  EXPECT_SEC_WRITE32(base_ + info_page.cfg_offset, GetParam().info_write_val);

  info_page = InfoPages().at(kFlashCtrlInfoPageBootData1);
  EXPECT_SEC_READ32(base_ + info_page.cfg_offset,
                    FLASH_CTRL_BANK0_INFO0_PAGE_CFG_0_REG_RESVAL);
  EXPECT_SEC_WRITE32(base_ + info_page.cfg_offset, GetParam().info_write_val);

  flash_ctrl_init();
}

INSTANTIATE_TEST_SUITE_P(AllCases, InitTest,
                         testing::Values(
                             // Scrambling.
                             InitCase{
                                 .cfg = {.scrambling = kMultiBitBool4True,
                                         .ecc = kMultiBitBool4False,
                                         .he = kMultiBitBool4False},
                                 .info_write_val = 0x9969996,
                                 .data_write_val = 0x996999,
                             },
                             // ECC.
                             InitCase{
                                 .cfg = {.scrambling = kMultiBitBool4False,
                                         .ecc = kMultiBitBool4True,
                                         .he = kMultiBitBool4False},
                                 .info_write_val = 0x9699996,
                                 .data_write_val = 0x969999,
                             },
                             // High endurance.
                             InitCase{
                                 .cfg = {.scrambling = kMultiBitBool4False,
                                         .ecc = kMultiBitBool4False,
                                         .he = kMultiBitBool4True},
                                 .info_write_val = 0x6999996,
                                 .data_write_val = 0x699999,
                             },
                             // Scrambling and ECC.
                             InitCase{
                                 .cfg = {.scrambling = kMultiBitBool4True,
                                         .ecc = kMultiBitBool4True,
                                         .he = kMultiBitBool4False},
                                 .info_write_val = 0x9669996,
                                 .data_write_val = 0x966999,
                             }));

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

TEST_F(TransferTest, ReadInfoOk) {
  // Address of the `kFlashCtrlInfoPageOwnerSlot0` page, see `info_page_addr`.
  const uint32_t addr =
      1 * FLASH_CTRL_PARAM_BYTES_PER_BANK + 2 * FLASH_CTRL_PARAM_BYTES_PER_PAGE;
  ExpectTransferStart(1, 0, 0, FLASH_CTRL_CONTROL_OP_VALUE_READ,
                      addr + 0x01234567, words_.size());
  ExpectReadData(words_);
  ExpectWaitForDone(true, false);
  std::vector<uint32_t> words_out(words_.size());
  EXPECT_EQ(flash_ctrl_info_read(kFlashCtrlInfoPageOwnerSlot0, 0x01234567,
                                 words_.size(), &words_out.front()),
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

TEST_F(TransferTest, ProgInfoOk) {
  // Address of the `kFlashCtrlInfoPageOwnerSlot0` page, see `info_page_addr`.
  const uint32_t addr =
      1 * FLASH_CTRL_PARAM_BYTES_PER_BANK + 2 * FLASH_CTRL_PARAM_BYTES_PER_PAGE;
  ExpectTransferStart(1, 0, 0, FLASH_CTRL_CONTROL_OP_VALUE_PROG,
                      addr + 0x01234567, words_.size());
  ExpectProgData(words_);
  ExpectWaitForDone(true, false);
  EXPECT_EQ(flash_ctrl_info_write(kFlashCtrlInfoPageOwnerSlot0, 0x01234567,
                                  words_.size(), &words_.front()),
            kErrorOk);
}

TEST_F(TransferTest, EraseDataPageOk) {
  ExpectTransferStart(0, 0, 0, FLASH_CTRL_CONTROL_OP_VALUE_ERASE, 0x01234567,
                      1);
  ExpectWaitForDone(true, false);
  EXPECT_EQ(flash_ctrl_data_erase(0x01234567, kFlashCtrlEraseTypePage),
            kErrorOk);
}

TEST_F(TransferTest, EraseInfoPageOk) {
  // Address of the `kFlashCtrlInfoPageOwnerSlot0` page, see `info_page_addr`.
  const uint32_t addr =
      1 * FLASH_CTRL_PARAM_BYTES_PER_BANK + 2 * FLASH_CTRL_PARAM_BYTES_PER_PAGE;
  ExpectTransferStart(1, 0, 0, FLASH_CTRL_CONTROL_OP_VALUE_ERASE, addr, 1);
  ExpectWaitForDone(true, false);
  EXPECT_EQ(flash_ctrl_info_erase(kFlashCtrlInfoPageOwnerSlot0,
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

TEST_F(ExecTest, Set) {
  EXPECT_SEC_WRITE32(base_ + FLASH_CTRL_EXEC_REG_OFFSET, UINT32_MAX);
  flash_ctrl_exec_set(UINT32_MAX);
}

struct PermsSetCase {
  /**
   * Access permissions to set.
   */
  flash_ctrl_perms_t perms;
  /**
   * Expected value to be read from the info config register.
   */
  uint32_t info_read_val;
  /**
   * Expected value to be written to the info config register.
   */
  uint32_t info_write_val;
  /**
   * Expected value to be read from the data config register.
   */
  uint32_t data_read_val;
  /**
   * Expected value to be written to the data config register.
   */
  uint32_t data_write_val;
};

class FlashCtrlPermsSetTest : public FlashCtrlTest,
                              public testing::WithParamInterface<PermsSetCase> {
};

TEST_P(FlashCtrlPermsSetTest, InfoPermsSet) {
  for (const auto &it : InfoPages()) {
    EXPECT_SEC_READ32(base_ + it.second.cfg_offset, GetParam().info_read_val);
    EXPECT_SEC_WRITE32(base_ + it.second.cfg_offset, GetParam().info_write_val);

    flash_ctrl_info_perms_set(it.first, GetParam().perms);
  }
}

TEST_P(FlashCtrlPermsSetTest, DataDefaultPermsSet) {
  EXPECT_SEC_READ32(base_ + FLASH_CTRL_DEFAULT_REGION_REG_OFFSET,
                    GetParam().data_read_val);
  EXPECT_SEC_WRITE32(base_ + FLASH_CTRL_DEFAULT_REGION_REG_OFFSET,
                     GetParam().data_write_val);

  flash_ctrl_data_default_perms_set(GetParam().perms);
}

INSTANTIATE_TEST_SUITE_P(AllCases, FlashCtrlPermsSetTest,
                         testing::Values(
                             // Read.
                             PermsSetCase{
                                 .perms = {.read = kMultiBitBool4True,
                                           .write = kMultiBitBool4False,
                                           .erase = kMultiBitBool4False},
                                 .info_read_val = 0x9999999,
                                 .info_write_val = 0x9999966,
                                 .data_read_val = 0x999999,
                                 .data_write_val = 0x999996,
                             },
                             PermsSetCase{
                                 .perms = {.read = kMultiBitBool4True,
                                           .write = kMultiBitBool4False,
                                           .erase = kMultiBitBool4False},
                                 .info_read_val = 0x6666666,
                                 .info_write_val = 0x6669966,
                                 .data_read_val = 0x666666,
                                 .data_write_val = 0x666996,
                             },
                             // Write.
                             PermsSetCase{
                                 .perms = {.read = kMultiBitBool4False,
                                           .write = kMultiBitBool4True,
                                           .erase = kMultiBitBool4False},
                                 .info_read_val = 0x9999999,
                                 .info_write_val = 0x9999696,
                                 .data_read_val = 0x999999,
                                 .data_write_val = 0x999969,
                             },
                             PermsSetCase{
                                 .perms = {.read = kMultiBitBool4False,
                                           .write = kMultiBitBool4True,
                                           .erase = kMultiBitBool4False},
                                 .info_read_val = 0x6666666,
                                 .info_write_val = 0x6669696,
                                 .data_read_val = 0x666666,
                                 .data_write_val = 0x666969,
                             },
                             // Erase.
                             PermsSetCase{
                                 .perms = {.read = kMultiBitBool4False,
                                           .write = kMultiBitBool4False,
                                           .erase = kMultiBitBool4True},
                                 .info_read_val = 0x9999999,
                                 .info_write_val = 0x9996996,
                                 .data_read_val = 0x999999,
                                 .data_write_val = 0x999699,
                             },
                             PermsSetCase{
                                 .perms = {.read = kMultiBitBool4False,
                                           .write = kMultiBitBool4False,
                                           .erase = kMultiBitBool4True},
                                 .info_read_val = 0x6666666,
                                 .info_write_val = 0x6666996,
                                 .data_read_val = 0x666666,
                                 .data_write_val = 0x666699,
                             },
                             // Write and erase.
                             PermsSetCase{
                                 .perms = {.read = kMultiBitBool4False,
                                           .write = kMultiBitBool4True,
                                           .erase = kMultiBitBool4True},
                                 .info_read_val = 0x9999999,
                                 .info_write_val = 0x9996696,
                                 .data_read_val = 0x999999,
                                 .data_write_val = 0x999669},
                             PermsSetCase{
                                 .perms = {.read = kMultiBitBool4False,
                                           .write = kMultiBitBool4True,
                                           .erase = kMultiBitBool4True},
                                 .info_read_val = 0x6666666,
                                 .info_write_val = 0x6666696,
                                 .data_read_val = 0x666666,
                                 .data_write_val = 0x666669,
                             }));

struct CfgSetCase {
  /**
   * Configuration settings to set.
   */
  flash_ctrl_cfg_t cfg;
  /**
   * Expected value to be read from the info config register.
   */
  uint32_t info_read_val;
  /**
   * Expected value to be written to the info config register.
   */
  uint32_t info_write_val;
  /**
   * Expected value to be read from the data config register.
   */
  uint32_t data_read_val;
  /**
   * Expected value to be written to the data config register.
   */
  uint32_t data_write_val;
};

class FlashCtrlCfgSetTest : public FlashCtrlTest,
                            public testing::WithParamInterface<CfgSetCase> {};

TEST_P(FlashCtrlCfgSetTest, InfoCfgSet) {
  for (const auto &it : InfoPages()) {
    EXPECT_SEC_READ32(base_ + it.second.cfg_offset, GetParam().info_read_val);
    EXPECT_SEC_WRITE32(base_ + it.second.cfg_offset, GetParam().info_write_val);

    flash_ctrl_info_cfg_set(it.first, GetParam().cfg);
  }
}

TEST_P(FlashCtrlCfgSetTest, DataDefaultCfgSet) {
  EXPECT_SEC_READ32(base_ + FLASH_CTRL_DEFAULT_REGION_REG_OFFSET,
                    GetParam().data_read_val);
  EXPECT_SEC_WRITE32(base_ + FLASH_CTRL_DEFAULT_REGION_REG_OFFSET,
                     GetParam().data_write_val);

  flash_ctrl_data_default_cfg_set(GetParam().cfg);
}

INSTANTIATE_TEST_SUITE_P(AllCases, FlashCtrlCfgSetTest,
                         testing::Values(
                             // Scrambling.
                             CfgSetCase{
                                 .cfg = {.scrambling = kMultiBitBool4True,
                                         .ecc = kMultiBitBool4False,
                                         .he = kMultiBitBool4False},
                                 .info_read_val = 0x9999999,
                                 .info_write_val = 0x9969996,
                                 .data_read_val = 0x999999,
                                 .data_write_val = 0x996999,
                             },
                             CfgSetCase{
                                 .cfg = {.scrambling = kMultiBitBool4True,
                                         .ecc = kMultiBitBool4False,
                                         .he = kMultiBitBool4False},
                                 .info_read_val = 0x6666666,
                                 .info_write_val = 0x9966666,
                                 .data_read_val = 0x666666,
                                 .data_write_val = 0x996666,
                             },
                             // ECC.
                             CfgSetCase{
                                 .cfg = {.scrambling = kMultiBitBool4False,
                                         .ecc = kMultiBitBool4True,
                                         .he = kMultiBitBool4False},
                                 .info_read_val = 0x9999999,
                                 .info_write_val = 0x9699996,
                                 .data_read_val = 0x999999,
                                 .data_write_val = 0x969999,
                             },
                             CfgSetCase{
                                 .cfg = {.scrambling = kMultiBitBool4False,
                                         .ecc = kMultiBitBool4True,
                                         .he = kMultiBitBool4False},
                                 .info_read_val = 0x6666666,
                                 .info_write_val = 0x9696666,
                                 .data_read_val = 0x666666,
                                 .data_write_val = 0x969666,
                             },
                             // High endurance.
                             CfgSetCase{
                                 .cfg = {.scrambling = kMultiBitBool4False,
                                         .ecc = kMultiBitBool4False,
                                         .he = kMultiBitBool4True},
                                 .info_read_val = 0x9999999,
                                 .info_write_val = 0x6999996,
                                 .data_read_val = 0x999999,
                                 .data_write_val = 0x699999,
                             },
                             CfgSetCase{
                                 .cfg = {.scrambling = kMultiBitBool4False,
                                         .ecc = kMultiBitBool4False,
                                         .he = kMultiBitBool4True},
                                 .info_read_val = 0x6666666,
                                 .info_write_val = 0x6996666,
                                 .data_read_val = 0x666666,
                                 .data_write_val = 0x699666,
                             },
                             // Scrambling and ECC.
                             CfgSetCase{
                                 .cfg = {.scrambling = kMultiBitBool4True,
                                         .ecc = kMultiBitBool4True,
                                         .he = kMultiBitBool4False},
                                 .info_read_val = 0x9999999,
                                 .info_write_val = 0x9669996,
                                 .data_read_val = 0x999999,
                                 .data_write_val = 0x966999,
                             },
                             CfgSetCase{
                                 .cfg = {.scrambling = kMultiBitBool4True,
                                         .ecc = kMultiBitBool4True,
                                         .he = kMultiBitBool4False},
                                 .info_read_val = 0x6666666,
                                 .info_write_val = 0x9666666,
                                 .data_read_val = 0x666666,
                                 .data_write_val = 0x966666,
                             }));

TEST_F(FlashCtrlTest, CreatorInfoLockdown) {
  std::array<flash_ctrl_info_page_t, 7> no_owner_access = {
      kFlashCtrlInfoPageCreatorSecret,   kFlashCtrlInfoPageOwnerSecret,
      kFlashCtrlInfoPageWaferAuthSecret, kFlashCtrlInfoPageBootData0,
      kFlashCtrlInfoPageBootData1,       kFlashCtrlInfoPageOwnerSlot0,
      kFlashCtrlInfoPageOwnerSlot1,
  };
  for (auto page : no_owner_access) {
    auto info_page = InfoPages().at(page);
    EXPECT_SEC_WRITE32(base_ + info_page.cfg_offset, 0);
    EXPECT_SEC_WRITE32(base_ + info_page.cfg_wen_offset, 0);
  }

  flash_ctrl_creator_info_pages_lockdown();
}

TEST_F(FlashCtrlTest, BankErasePermsSet) {
  EXPECT_SEC_WRITE32_SHADOWED(
      base_ + FLASH_CTRL_MP_BANK_CFG_SHADOWED_REG_OFFSET,
      {
          {FLASH_CTRL_MP_BANK_CFG_SHADOWED_ERASE_EN_0_BIT, 1},
          {FLASH_CTRL_MP_BANK_CFG_SHADOWED_ERASE_EN_1_BIT, 1},
      });
  flash_ctrl_bank_erase_perms_set(kHardenedBoolTrue);

  EXPECT_SEC_WRITE32_SHADOWED(
      base_ + FLASH_CTRL_MP_BANK_CFG_SHADOWED_REG_OFFSET, 0);
  flash_ctrl_bank_erase_perms_set(kHardenedBoolFalse);
}

struct EraseVerifyCase {
  /**
   * Address.
   */
  uint32_t addr;
  /**
   * Truncated address aligned to closest lower page/bank.
   */
  uint32_t aligned_addr;
  /**
   * Erase type.
   */
  flash_ctrl_erase_type_t erase_type;
  /**
   * Value of the last word read from flash (for testing failure cases).
   */
  uint32_t last_word_val;
  /**
   * Expected return value.
   */
  rom_error_t error;
};

class EraseVerifyTest : public FlashCtrlTest,
                        public testing::WithParamInterface<EraseVerifyCase> {};

TEST_P(EraseVerifyTest, DataEraseVerify) {
  size_t byte_count;
  switch (GetParam().erase_type) {
    case kFlashCtrlEraseTypeBank:
      byte_count = FLASH_CTRL_PARAM_BYTES_PER_BANK;
      break;
    case kFlashCtrlEraseTypePage:
      byte_count = FLASH_CTRL_PARAM_BYTES_PER_PAGE;
      break;
    default:
      FAIL();
  }

  size_t i = 0;
  for (; i < byte_count - sizeof(uint32_t); i += sizeof(uint32_t)) {
    EXPECT_ABS_READ32(
        TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR + GetParam().aligned_addr + i,
        kFlashCtrlErasedWord);
  }
  EXPECT_ABS_READ32(
      TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR + GetParam().aligned_addr + i,
      GetParam().last_word_val);

  EXPECT_EQ(
      flash_ctrl_data_erase_verify(GetParam().addr, GetParam().erase_type),
      GetParam().error);
}

INSTANTIATE_TEST_SUITE_P(
    AllCases, EraseVerifyTest,
    testing::Values(
        // Verify first page.
        EraseVerifyCase{
            .addr = 0,
            .aligned_addr = 0,
            .erase_type = kFlashCtrlEraseTypePage,
            .last_word_val = kFlashCtrlErasedWord,
            .error = kErrorOk,
        },
        // Verify 10th page, unaligned address.
        EraseVerifyCase{
            .addr = 10 * FLASH_CTRL_PARAM_BYTES_PER_PAGE + 128,
            .aligned_addr = 10 * FLASH_CTRL_PARAM_BYTES_PER_PAGE,
            .erase_type = kFlashCtrlEraseTypePage,
            .last_word_val = kFlashCtrlErasedWord,
            .error = kErrorOk,
        },
        // Fail to verify 10th page, unaligned address.
        EraseVerifyCase{
            .addr = 10 * FLASH_CTRL_PARAM_BYTES_PER_PAGE + 128,
            .aligned_addr = 10 * FLASH_CTRL_PARAM_BYTES_PER_PAGE,
            .erase_type = kFlashCtrlEraseTypePage,
            .last_word_val = 0xfffffff0,
            .error = kErrorFlashCtrlDataEraseVerify,
        }  // Note: No cases for bank erases since the test times out due to
           // large number of expectations.
        ));

}  // namespace
}  // namespace flash_ctrl_unittest
