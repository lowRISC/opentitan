// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom/bootstrap.h"

#include <cstring>
#include <limits>

#include "gtest/gtest.h"
#include "sw/device/lib/base/mock_abs_mmio.h"
#include "sw/device/silicon_creator/lib/base/chip.h"
#include "sw/device/silicon_creator/lib/bootstrap_unittest_util.h"
#include "sw/device/silicon_creator/lib/drivers/mock_flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/mock_otp.h"
#include "sw/device/silicon_creator/lib/drivers/mock_rstmgr.h"
#include "sw/device/silicon_creator/lib/drivers/mock_spi_device.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

#include "flash_ctrl_regs.h"
#include "gpio_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"

namespace bootstrap_unittest {
namespace {

using bootstrap_unittest_util::BootstrapTest;
using bootstrap_unittest_util::ChipEraseCmd;
using bootstrap_unittest_util::PageProgramCmd;
using bootstrap_unittest_util::ResetCmd;
using bootstrap_unittest_util::SectorEraseCmd;

using ::testing::NotNull;
using ::testing::Return;

MATCHER_P(HasBytes, bytes, "") {
  return std::memcmp(arg, bytes.data(), bytes.size()) == 0;
}

TEST_F(BootstrapTest, RequestedDisabled) {
  EXPECT_CALL(otp_,
              read32(OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_BOOTSTRAP_DIS_OFFSET))
      .WillOnce(Return(kHardenedBoolTrue));

  EXPECT_EQ(bootstrap_requested(), kHardenedBoolFalse);
}

TEST_F(BootstrapTest, RequestedEnabled) {
  EXPECT_CALL(otp_,
              read32(OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_BOOTSTRAP_DIS_OFFSET))
      .WillOnce(Return(kHardenedBoolFalse));
  EXPECT_ABS_READ32(TOP_EARLGREY_GPIO_BASE_ADDR + GPIO_DATA_IN_REG_OFFSET,
                    SW_STRAP_BOOTSTRAP);
  EXPECT_EQ(bootstrap_requested(), kHardenedBoolTrue);

  EXPECT_CALL(otp_,
              read32(OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_BOOTSTRAP_DIS_OFFSET))
      .WillOnce(Return(kHardenedBoolFalse));
  EXPECT_ABS_READ32(TOP_EARLGREY_GPIO_BASE_ADDR + GPIO_DATA_IN_REG_OFFSET,
                    ~SW_STRAP_BOOTSTRAP);
  EXPECT_EQ(bootstrap_requested(), kHardenedBoolFalse);
}

TEST_F(BootstrapTest, PayloadOverflowErase) {
  ExpectBootstrapRequestCheck(true);
  EXPECT_CALL(spi_device_, Init());
  EXPECT_CALL(spi_device_, CmdGet(NotNull()))
      .WillOnce(Return(kErrorSpiDevicePayloadOverflow));

  EXPECT_EQ(bootstrap(), kErrorSpiDevicePayloadOverflow);
}

TEST_F(BootstrapTest, PayloadOverflowProgram) {
  // Erase
  ExpectBootstrapRequestCheck(true);
  EXPECT_CALL(spi_device_, Init());
  ExpectSpiCmd(ChipEraseCmd());
  ExpectSpiFlashStatusGet(true);
  ExpectFlashCtrlChipErase(kErrorOk, kErrorOk);
  // Verify
  ExpectFlashCtrlEraseVerify(kErrorOk, kErrorOk);
  EXPECT_CALL(spi_device_, FlashStatusClear());
  // Program
  EXPECT_CALL(spi_device_, CmdGet(NotNull()))
      .WillOnce(Return(kErrorSpiDevicePayloadOverflow));

  EXPECT_EQ(bootstrap(), kErrorSpiDevicePayloadOverflow);
}

TEST_F(BootstrapTest, BootstrapSimple) {
  // Erase
  ExpectBootstrapRequestCheck(true);
  EXPECT_CALL(spi_device_, Init());
  ExpectSpiCmd(ChipEraseCmd());
  ExpectSpiFlashStatusGet(true);
  ExpectFlashCtrlChipErase(kErrorOk, kErrorOk);
  // Verify
  ExpectFlashCtrlEraseVerify(kErrorOk, kErrorOk);
  EXPECT_CALL(spi_device_, FlashStatusClear());
  // Program
  auto cmd = PageProgramCmd(0, 16);
  ExpectSpiCmd(cmd);
  ExpectSpiFlashStatusGet(true);

  std::vector<uint8_t> flash_bytes(cmd.payload,
                                   cmd.payload + cmd.payload_byte_count);

  ExpectFlashCtrlWriteEnable();
  EXPECT_CALL(flash_ctrl_, DataWrite(0, 4, HasBytes(flash_bytes)))
      .WillOnce(Return(kErrorOk));
  ExpectFlashCtrlAllDisable();

  EXPECT_CALL(spi_device_, FlashStatusClear());
  // Reset
  ExpectSpiCmd(ResetCmd());
  EXPECT_CALL(rstmgr_, Reset());

  EXPECT_EQ(bootstrap(), kErrorUnknown);
}

TEST_F(BootstrapTest, BootstrapOddPayload) {
  // Erase
  ExpectBootstrapRequestCheck(true);
  EXPECT_CALL(spi_device_, Init());
  ExpectSpiCmd(ChipEraseCmd());
  ExpectSpiFlashStatusGet(true);
  ExpectFlashCtrlChipErase(kErrorOk, kErrorOk);
  // Verify
  ExpectFlashCtrlEraseVerify(kErrorOk, kErrorOk);
  EXPECT_CALL(spi_device_, FlashStatusClear());
  // Program
  auto cmd = PageProgramCmd(0, 17);
  ExpectSpiCmd(cmd);
  ExpectSpiFlashStatusGet(true);

  std::vector<uint8_t> flash_bytes(cmd.payload,
                                   cmd.payload + cmd.payload_byte_count);
  for (size_t i = 0; i < 7; ++i) {
    flash_bytes.push_back(0xff);
  }

  ExpectFlashCtrlWriteEnable();
  EXPECT_CALL(flash_ctrl_, DataWrite(cmd.address, 6, HasBytes(flash_bytes)))
      .WillOnce(Return(kErrorOk));
  ExpectFlashCtrlAllDisable();

  EXPECT_CALL(spi_device_, FlashStatusClear());
  // Reset
  ExpectSpiCmd(ResetCmd());
  EXPECT_CALL(rstmgr_, Reset());

  EXPECT_EQ(bootstrap(), kErrorUnknown);
}

TEST_F(BootstrapTest, BootstrapMisalignedAddrLongPayload) {
  // Erase
  ExpectBootstrapRequestCheck(true);
  EXPECT_CALL(spi_device_, Init());
  ExpectSpiCmd(ChipEraseCmd());
  ExpectSpiFlashStatusGet(true);
  ExpectFlashCtrlChipErase(kErrorOk, kErrorOk);
  // Verify
  ExpectFlashCtrlEraseVerify(kErrorOk, kErrorOk);
  EXPECT_CALL(spi_device_, FlashStatusClear());
  // Program
  auto cmd = PageProgramCmd(0xfff0, 256);
  ExpectSpiCmd(cmd);
  ExpectSpiFlashStatusGet(true);

  std::vector<uint8_t> flash_bytes_0(cmd.payload, cmd.payload + 16);
  std::vector<uint8_t> flash_bytes_1(cmd.payload + 16,
                                     cmd.payload + cmd.payload_byte_count);

  ExpectFlashCtrlWriteEnable();
  EXPECT_CALL(flash_ctrl_, DataWrite(0xfff0, 4, HasBytes(flash_bytes_0)))
      .WillOnce(Return(kErrorOk));
  EXPECT_CALL(flash_ctrl_, DataWrite(0xff00, 60, HasBytes(flash_bytes_1)))
      .WillOnce(Return(kErrorOk));
  ExpectFlashCtrlAllDisable();

  EXPECT_CALL(spi_device_, FlashStatusClear());
  // Reset
  ExpectSpiCmd(ResetCmd());
  EXPECT_CALL(rstmgr_, Reset());

  EXPECT_EQ(bootstrap(), kErrorUnknown);
}

TEST_F(BootstrapTest, BootstrapMisalignedAddrShortPayload) {
  // Erase
  ExpectBootstrapRequestCheck(true);
  EXPECT_CALL(spi_device_, Init());
  ExpectSpiCmd(ChipEraseCmd());
  ExpectSpiFlashStatusGet(true);
  ExpectFlashCtrlChipErase(kErrorOk, kErrorOk);
  // Verify
  ExpectFlashCtrlEraseVerify(kErrorOk, kErrorOk);
  EXPECT_CALL(spi_device_, FlashStatusClear());
  // Program
  auto cmd = PageProgramCmd(816, 8);
  ExpectSpiCmd(cmd);
  ExpectSpiFlashStatusGet(true);

  std::vector<uint8_t> flash_bytes(cmd.payload,
                                   cmd.payload + cmd.payload_byte_count);

  ExpectFlashCtrlWriteEnable();
  EXPECT_CALL(flash_ctrl_, DataWrite(816, 2, HasBytes(flash_bytes)))
      .WillOnce(Return(kErrorOk));
  ExpectFlashCtrlAllDisable();

  EXPECT_CALL(spi_device_, FlashStatusClear());
  // Reset
  ExpectSpiCmd(ResetCmd());
  EXPECT_CALL(rstmgr_, Reset());

  EXPECT_EQ(bootstrap(), kErrorUnknown);
}

TEST_F(BootstrapTest, BootstrapStartWithSectorErase) {
  // Erase
  ExpectBootstrapRequestCheck(true);
  EXPECT_CALL(spi_device_, Init());
  ExpectSpiCmd(SectorEraseCmd(0));
  ExpectSpiFlashStatusGet(true);
  ExpectFlashCtrlChipErase(kErrorOk, kErrorOk);
  // Verify
  ExpectFlashCtrlEraseVerify(kErrorOk, kErrorOk);
  EXPECT_CALL(spi_device_, FlashStatusClear());
  // Program
  auto cmd = PageProgramCmd(0, 16);
  ExpectSpiCmd(cmd);
  ExpectSpiFlashStatusGet(true);

  std::vector<uint8_t> flash_bytes(cmd.payload,
                                   cmd.payload + cmd.payload_byte_count);

  ExpectFlashCtrlWriteEnable();
  EXPECT_CALL(flash_ctrl_,
              DataWrite(cmd.address, cmd.payload_byte_count / sizeof(uint32_t),
                        HasBytes(flash_bytes)))
      .WillOnce(Return(kErrorOk));
  ExpectFlashCtrlAllDisable();

  EXPECT_CALL(spi_device_, FlashStatusClear());
  // Reset
  ExpectSpiCmd(ResetCmd());
  EXPECT_CALL(rstmgr_, Reset());

  EXPECT_EQ(bootstrap(), kErrorUnknown);
}

TEST_F(BootstrapTest, BootstrapProgramWithErase) {
  // Erase
  ExpectBootstrapRequestCheck(true);
  EXPECT_CALL(spi_device_, Init());
  ExpectSpiCmd(ChipEraseCmd());
  ExpectSpiFlashStatusGet(true);
  ExpectFlashCtrlChipErase(kErrorOk, kErrorOk);
  // Verify
  ExpectFlashCtrlEraseVerify(kErrorOk, kErrorOk);
  EXPECT_CALL(spi_device_, FlashStatusClear());
  // Program
  auto cmd = PageProgramCmd(0, 16);
  ExpectSpiCmd(cmd);
  ExpectSpiFlashStatusGet(true);

  std::vector<uint8_t> flash_bytes(cmd.payload,
                                   cmd.payload + cmd.payload_byte_count);

  ExpectFlashCtrlWriteEnable();
  EXPECT_CALL(flash_ctrl_,
              DataWrite(cmd.address, cmd.payload_byte_count / sizeof(uint32_t),
                        HasBytes(flash_bytes)))
      .WillOnce(Return(kErrorOk));
  ExpectFlashCtrlAllDisable();

  EXPECT_CALL(spi_device_, FlashStatusClear());
  // Chip erase
  ExpectSpiCmd(ChipEraseCmd());
  ExpectSpiFlashStatusGet(true);
  ExpectFlashCtrlChipErase(kErrorOk, kErrorOk);
  EXPECT_CALL(spi_device_, FlashStatusClear());
  // Sector erase
  ExpectSpiCmd(SectorEraseCmd(0));
  ExpectSpiFlashStatusGet(true);
  ExpectFlashCtrlSectorErase(kErrorOk, kErrorOk, 0);
  EXPECT_CALL(spi_device_, FlashStatusClear());

  // Reset
  ExpectSpiCmd(ResetCmd());
  EXPECT_CALL(rstmgr_, Reset());

  EXPECT_EQ(bootstrap(), kErrorUnknown);
}

TEST_F(BootstrapTest, MisalignedEraseAddress) {
  // Erase
  ExpectBootstrapRequestCheck(true);
  EXPECT_CALL(spi_device_, Init());
  ExpectSpiCmd(ChipEraseCmd());
  ExpectSpiFlashStatusGet(true);
  ExpectFlashCtrlChipErase(kErrorOk, kErrorOk);
  // Verify
  ExpectFlashCtrlEraseVerify(kErrorOk, kErrorOk);
  EXPECT_CALL(spi_device_, FlashStatusClear());
  // Erase with misaligned and aligned addresses
  ExpectSpiCmd(SectorEraseCmd(5));
  ExpectSpiFlashStatusGet(true);
  ExpectFlashCtrlSectorErase(kErrorOk, kErrorOk, 0);
  EXPECT_CALL(spi_device_, FlashStatusClear());

  ExpectSpiCmd(SectorEraseCmd(4096));
  ExpectSpiFlashStatusGet(true);
  ExpectFlashCtrlSectorErase(kErrorOk, kErrorOk, 4096);
  EXPECT_CALL(spi_device_, FlashStatusClear());

  ExpectSpiCmd(SectorEraseCmd(8195));
  ExpectSpiFlashStatusGet(true);
  ExpectFlashCtrlSectorErase(kErrorOk, kErrorOk, 8192);
  EXPECT_CALL(spi_device_, FlashStatusClear());
  // Reset
  ExpectSpiCmd(ResetCmd());
  EXPECT_CALL(rstmgr_, Reset());

  EXPECT_EQ(bootstrap(), kErrorUnknown);
}

TEST_F(BootstrapTest, IgnoredCommands) {
  // Phase 1: Erase
  ExpectBootstrapRequestCheck(true);
  EXPECT_CALL(spi_device_, Init());
  ExpectSpiCmd(ChipEraseCmd());  // Ignored, missing WREN.
  ExpectSpiFlashStatusGet(false);
  ExpectSpiCmd(ResetCmd());  // Ignored, not supported.
  ExpectSpiFlashStatusGet(true);
  EXPECT_CALL(spi_device_, FlashStatusClear());
  ExpectSpiCmd(ChipEraseCmd());
  ExpectSpiFlashStatusGet(true);
  ExpectFlashCtrlChipErase(kErrorOk, kErrorOk);
  // Phase 1: Verify
  ExpectFlashCtrlEraseVerify(kErrorOk, kErrorOk);
  EXPECT_CALL(spi_device_, FlashStatusClear());
  // Phase 2: Erase/Program
  ExpectSpiCmd(SectorEraseCmd(0));
  ExpectSpiFlashStatusGet(false);
  ExpectSpiCmd(ChipEraseCmd());
  ExpectSpiFlashStatusGet(false);
  ExpectSpiCmd(PageProgramCmd(0, 16));
  ExpectSpiFlashStatusGet(false);
  // Reset
  ExpectSpiCmd(ResetCmd());
  EXPECT_CALL(rstmgr_, Reset());

  EXPECT_EQ(bootstrap(), kErrorUnknown);
}

TEST_F(BootstrapTest, EraseBank0Error) {
  ExpectBootstrapRequestCheck(true);
  EXPECT_CALL(spi_device_, Init());
  ExpectSpiCmd(ChipEraseCmd());
  ExpectSpiFlashStatusGet(true);
  ExpectFlashCtrlChipErase(kErrorUnknown, kErrorOk);

  EXPECT_EQ(bootstrap(), kErrorUnknown);
}

TEST_F(BootstrapTest, EraseBank1Error) {
  ExpectBootstrapRequestCheck(true);
  EXPECT_CALL(spi_device_, Init());
  ExpectSpiCmd(ChipEraseCmd());
  ExpectSpiFlashStatusGet(true);
  ExpectFlashCtrlChipErase(kErrorOk, kErrorUnknown);

  EXPECT_EQ(bootstrap(), kErrorUnknown);
}

TEST_F(BootstrapTest, EraseVerifyBank0Error) {
  // Erase
  ExpectBootstrapRequestCheck(true);
  EXPECT_CALL(spi_device_, Init());
  ExpectSpiCmd(ChipEraseCmd());
  ExpectSpiFlashStatusGet(true);
  ExpectFlashCtrlChipErase(kErrorOk, kErrorOk);
  // Verify
  ExpectFlashCtrlEraseVerify(kErrorUnknown, kErrorOk);

  EXPECT_EQ(bootstrap(), kErrorUnknown);
}

TEST_F(BootstrapTest, EraseVerifyBank1Error) {
  // Erase
  ExpectBootstrapRequestCheck(true);
  EXPECT_CALL(spi_device_, Init());
  ExpectSpiCmd(ChipEraseCmd());
  ExpectSpiFlashStatusGet(true);
  ExpectFlashCtrlChipErase(kErrorOk, kErrorOk);
  // Verify
  ExpectFlashCtrlEraseVerify(kErrorOk, kErrorUnknown);

  EXPECT_EQ(bootstrap(), kErrorUnknown);
}

TEST_F(BootstrapTest, DataWriteError) {
  // Erase
  ExpectBootstrapRequestCheck(true);
  EXPECT_CALL(spi_device_, Init());
  ExpectSpiCmd(ChipEraseCmd());
  ExpectSpiFlashStatusGet(true);
  ExpectFlashCtrlChipErase(kErrorOk, kErrorOk);
  // Verify
  ExpectFlashCtrlEraseVerify(kErrorOk, kErrorOk);
  EXPECT_CALL(spi_device_, FlashStatusClear());
  // Program
  auto cmd = PageProgramCmd(0, 16);
  ExpectSpiCmd(cmd);
  ExpectSpiFlashStatusGet(true);

  std::vector<uint8_t> flash_bytes(cmd.payload,
                                   cmd.payload + cmd.payload_byte_count);

  ExpectFlashCtrlWriteEnable();
  EXPECT_CALL(flash_ctrl_,
              DataWrite(cmd.address, cmd.payload_byte_count / sizeof(uint32_t),
                        HasBytes(flash_bytes)))
      .WillOnce(Return(kErrorUnknown));
  ExpectFlashCtrlAllDisable();

  EXPECT_EQ(bootstrap(), kErrorUnknown);
}

TEST_F(BootstrapTest, DataWriteErrorMisalignedAddr) {
  // Erase
  ExpectBootstrapRequestCheck(true);
  EXPECT_CALL(spi_device_, Init());
  ExpectSpiCmd(ChipEraseCmd());
  ExpectSpiFlashStatusGet(true);
  ExpectFlashCtrlChipErase(kErrorOk, kErrorOk);
  // Verify
  ExpectFlashCtrlEraseVerify(kErrorOk, kErrorOk);
  EXPECT_CALL(spi_device_, FlashStatusClear());
  // Program
  auto cmd = PageProgramCmd(0xf0, 16);
  ExpectSpiCmd(cmd);
  ExpectSpiFlashStatusGet(true);

  std::vector<uint8_t> flash_bytes(cmd.payload,
                                   cmd.payload + cmd.payload_byte_count);

  ExpectFlashCtrlWriteEnable();
  EXPECT_CALL(flash_ctrl_, DataWrite(0xf0, 4, HasBytes(flash_bytes)))
      .WillOnce(Return(kErrorUnknown));
  ExpectFlashCtrlAllDisable();

  EXPECT_EQ(bootstrap(), kErrorUnknown);
}

TEST_F(BootstrapTest, BadProgramAddress) {
  // Erase
  ExpectBootstrapRequestCheck(true);
  EXPECT_CALL(spi_device_, Init());
  ExpectSpiCmd(ChipEraseCmd());
  ExpectSpiFlashStatusGet(true);
  ExpectFlashCtrlChipErase(kErrorOk, kErrorOk);
  // Verify
  ExpectFlashCtrlEraseVerify(kErrorOk, kErrorOk);
  EXPECT_CALL(spi_device_, FlashStatusClear());
  // Program
  auto page_program_cmd = PageProgramCmd(3, 16);
  ExpectSpiCmd(page_program_cmd);
  ExpectSpiFlashStatusGet(true);

  EXPECT_EQ(bootstrap(), kErrorBootstrapProgramAddress);
}

TEST_F(BootstrapTest, BadEraseAddress) {
  // Erase
  ExpectBootstrapRequestCheck(true);
  EXPECT_CALL(spi_device_, Init());
  ExpectSpiCmd(ChipEraseCmd());
  ExpectSpiFlashStatusGet(true);
  ExpectFlashCtrlChipErase(kErrorOk, kErrorOk);
  // Verify
  ExpectFlashCtrlEraseVerify(kErrorOk, kErrorOk);
  EXPECT_CALL(spi_device_, FlashStatusClear());
  // Erase
  ExpectSpiCmd(SectorEraseCmd(FLASH_CTRL_PARAM_BYTES_PER_BANK *
                              FLASH_CTRL_PARAM_REG_NUM_BANKS));
  ExpectSpiFlashStatusGet(true);

  EXPECT_EQ(bootstrap(), kErrorBootstrapEraseAddress);
}

TEST_F(BootstrapTest, NotRequested) {
  ExpectBootstrapRequestCheck(false);

  EXPECT_EQ(bootstrap(), kErrorBootstrapNotRequested);
}

}  // namespace
}  // namespace bootstrap_unittest
