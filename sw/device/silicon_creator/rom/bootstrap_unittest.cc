// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom/bootstrap.h"

#include <cstring>
#include <limits>

#include "gtest/gtest.h"
#include "sw/device/silicon_creator/lib/drivers/mock_ctn_sram.h"
#include "sw/device/silicon_creator/lib/drivers/mock_otp.h"
#include "sw/device/silicon_creator/lib/drivers/mock_rstmgr.h"
#include "sw/device/silicon_creator/lib/drivers/mock_spi_device.h"
#include "sw/lib/sw/device/base/mock_abs_mmio.h"
#include "sw/lib/sw/device/silicon_creator/base/chip.h"
#include "sw/lib/sw/device/silicon_creator/testing/rom_test.h"

#include "flash_ctrl_regs.h"
#include "gpio_regs.h"
#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"
#include "otp_ctrl_regs.h"

bool operator==(ctn_sram_perms_t lhs, ctn_sram_perms_t rhs) {
  return std::memcmp(&lhs, &rhs, sizeof(ctn_sram_perms_t)) == 0;
}

namespace bootstrap_unittest {
namespace {

using ::testing::DoAll;
using ::testing::NotNull;
using ::testing::Return;
using ::testing::SetArgPointee;

MATCHER_P(HasBytes, bytes, "") {
  return std::memcmp(arg, bytes.data(), bytes.size()) == 0;
}

class BootstrapTest : public rom_test::RomTest {
 protected:
  /**
   * Sets an expectation for a bootstrap request check.
   *
   * @param requested Whether bootstrap is requested.
   */
  void ExpectBootstrapRequestCheck(bool requested) {
    EXPECT_CALL(otp_,
                read32(OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_BOOTSTRAP_DIS_OFFSET))
        .WillOnce(Return(kHardenedBoolFalse));
    uint32_t pins = SW_STRAP_BOOTSTRAP;
    if (!requested) {
      pins = ~pins;
    }
    EXPECT_ABS_READ32(TOP_DARJEELING_GPIO_BASE_ADDR + GPIO_DATA_IN_REG_OFFSET,
                      pins);
  }

  /**
   * Sets an expectation for a spi flash command.
   *
   * @param cmd Command struct to output.
   */
  void ExpectSpiCmd(spi_device_cmd_t cmd) {
    EXPECT_CALL(spi_device_, CmdGet(NotNull()))
        .WillOnce(DoAll(SetArgPointee<0>(cmd), Return(kErrorOk)));
  }

  /**
   * Sets an expectation for getting the SPI flash status register.
   *
   * @param wel Value of the WEL bit.
   */
  void ExpectSpiFlashStatusGet(bool wel) {
    EXPECT_CALL(spi_device_, FlashStatusGet())
        .WillOnce(Return(wel << kSpiDeviceWelBit));
  }

  /**
   * Sets an expectation for enabling write for the data partition.
   */
  void ExpectCtnSramWriteEnable() {
    EXPECT_CALL(ctn_sram_, DataDefaultPermsSet((ctn_sram_perms_t){
                               .read = kMultiBitBool4False,
                               .write = kMultiBitBool4True,
                               .erase = kMultiBitBool4False,
                           }));
  }

  /**
   * Sets an expectation for disabling all permissions for the data partition.
   */
  void ExpectCtnSramAllDisable() {
    EXPECT_CALL(ctn_sram_, DataDefaultPermsSet((ctn_sram_perms_t){
                               .read = kMultiBitBool4False,
                               .write = kMultiBitBool4False,
                               .erase = kMultiBitBool4False,
                           }));
  }

  /**
   * Sets expectations for a chip erase.
   *
   * @param err0 Result of erase for the first bank.
   * @param err1 Result of erase for the second bank.
   */
  void ExpectCtnSramChipErase(rom_error_t err0, rom_error_t err1) {
    EXPECT_CALL(ctn_sram_, BankErasePermsSet(kHardenedBoolTrue));
    EXPECT_CALL(ctn_sram_, DataErase(0, kCtnSramEraseTypeBank))
        .WillOnce(Return(err0));
    EXPECT_CALL(ctn_sram_, DataErase(FLASH_CTRL_PARAM_BYTES_PER_BANK,
                                     kCtnSramEraseTypeBank))
        .WillOnce(Return(err1));
    EXPECT_CALL(ctn_sram_, BankErasePermsSet(kHardenedBoolFalse));
  }

  /**
   * Sets expectations for a sector erase.
   *
   * @param err0 Result of erase for the first page.
   * @param err1 Result of erase for the second page.
   * @param addr Erase start address.
   */
  void ExpectCtnSramSectorErase(rom_error_t err0, rom_error_t err1,
                                uint32_t addr) {
    EXPECT_CALL(ctn_sram_, DataDefaultPermsSet((ctn_sram_perms_t){
                               .read = kMultiBitBool4False,
                               .write = kMultiBitBool4False,
                               .erase = kMultiBitBool4True,
                           }));
    EXPECT_CALL(ctn_sram_, DataErase(addr, kCtnSramEraseTypePage))
        .WillOnce(Return(err0));
    EXPECT_CALL(ctn_sram_, DataErase(addr + FLASH_CTRL_PARAM_BYTES_PER_PAGE,
                                     kCtnSramEraseTypePage))
        .WillOnce(Return(err1));
    ExpectCtnSramAllDisable();
  }

  /**
   * Sets expectations for a chip erase verification.
   *
   * @param err0 Result of erase verification for the first bank.
   * @param err1 Result of erase verification for the second bank.
   */
  void ExpectCtnSramEraseVerify(rom_error_t err0, rom_error_t err1) {
    EXPECT_CALL(ctn_sram_, DataEraseVerify(0, kCtnSramEraseTypeBank))
        .WillOnce(Return(err0));
    EXPECT_CALL(ctn_sram_, DataEraseVerify(FLASH_CTRL_PARAM_BYTES_PER_BANK,
                                           kCtnSramEraseTypeBank))
        .WillOnce(Return(err1));
  }

  rom_test::MockAbsMmio mmio_;
  rom_test::MockCtnSram ctn_sram_;
  rom_test::MockOtp otp_;
  rom_test::MockRstmgr rstmgr_;
  rom_test::MockSpiDevice spi_device_;
};

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
  EXPECT_ABS_READ32(TOP_DARJEELING_GPIO_BASE_ADDR + GPIO_DATA_IN_REG_OFFSET,
                    SW_STRAP_BOOTSTRAP);
  EXPECT_EQ(bootstrap_requested(), kHardenedBoolTrue);

  EXPECT_CALL(otp_,
              read32(OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_BOOTSTRAP_DIS_OFFSET))
      .WillOnce(Return(kHardenedBoolFalse));
  EXPECT_ABS_READ32(TOP_DARJEELING_GPIO_BASE_ADDR + GPIO_DATA_IN_REG_OFFSET,
                    ~SW_STRAP_BOOTSTRAP);
  EXPECT_EQ(bootstrap_requested(), kHardenedBoolFalse);
}

/**
 * Returns a struct that represents a CHIP_ERASE command.
 *
 * @return A `spi_device_cmd_t` that represents a CHIP_ERASE command.
 */
spi_device_cmd_t ChipEraseCmd() {
  return {
      .opcode = kSpiDeviceOpcodeChipErase,
      .address = kSpiDeviceNoAddress,
      .payload_byte_count = 0,
      .payload = {},
  };
}

/**
 * Returns a struct that represents a SECTOR_ERASE command.
 *
 * @param address Address field of the command.
 * @return A `spi_device_cmd_t` that represents a SECTOR_ERASE command.
 */
spi_device_cmd_t SectorEraseCmd(uint32_t address) {
  return {
      .opcode = kSpiDeviceOpcodeSectorErase,
      .address = address,
      .payload_byte_count = 0,
      .payload = {},
  };
}

/**
 * Returns a struct that represents a PAGE_PROGRAM command.
 *
 * @param address Address field of the command.
 * @param payload_byte_count Payload size in bytes.
 * @return A `spi_device_cmd_t` that represents a PAGE_PROGRAM command.
 */
spi_device_cmd_t PageProgramCmd(uint32_t address, size_t payload_byte_count) {
  spi_device_cmd_t cmd{
      .opcode = kSpiDeviceOpcodePageProgram,
      .address = address,
      .payload_byte_count = payload_byte_count,
  };
  EXPECT_LE(payload_byte_count, kSpiDevicePayloadAreaNumBytes);
  for (size_t i = 0; i < payload_byte_count; ++i) {
    cmd.payload[i] = static_cast<uint8_t>(i);
  }

  return cmd;
}

spi_device_cmd_t ResetCmd() {
  return {
      .opcode = kSpiDeviceOpcodeReset,
      .address = kSpiDeviceNoAddress,
      .payload_byte_count = 0,
      .payload = {},
  };
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
  ExpectCtnSramChipErase(kErrorOk, kErrorOk);
  // Verify
  ExpectCtnSramEraseVerify(kErrorOk, kErrorOk);
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
  ExpectCtnSramChipErase(kErrorOk, kErrorOk);
  // Verify
  ExpectCtnSramEraseVerify(kErrorOk, kErrorOk);
  EXPECT_CALL(spi_device_, FlashStatusClear());
  // Program
  auto cmd = PageProgramCmd(0, 16);
  ExpectSpiCmd(cmd);
  ExpectSpiFlashStatusGet(true);

  std::vector<uint8_t> flash_bytes(cmd.payload,
                                   cmd.payload + cmd.payload_byte_count);

  ExpectCtnSramWriteEnable();
  EXPECT_CALL(ctn_sram_, DataWrite(0, 4, HasBytes(flash_bytes)))
      .WillOnce(Return(kErrorOk));
  ExpectCtnSramAllDisable();

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
  ExpectCtnSramChipErase(kErrorOk, kErrorOk);
  // Verify
  ExpectCtnSramEraseVerify(kErrorOk, kErrorOk);
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

  ExpectCtnSramWriteEnable();
  EXPECT_CALL(ctn_sram_, DataWrite(cmd.address, 6, HasBytes(flash_bytes)))
      .WillOnce(Return(kErrorOk));
  ExpectCtnSramAllDisable();

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
  ExpectCtnSramChipErase(kErrorOk, kErrorOk);
  // Verify
  ExpectCtnSramEraseVerify(kErrorOk, kErrorOk);
  EXPECT_CALL(spi_device_, FlashStatusClear());
  // Program
  auto cmd = PageProgramCmd(0xfff0, 256);
  ExpectSpiCmd(cmd);
  ExpectSpiFlashStatusGet(true);

  std::vector<uint8_t> flash_bytes_0(cmd.payload, cmd.payload + 16);
  std::vector<uint8_t> flash_bytes_1(cmd.payload + 16,
                                     cmd.payload + cmd.payload_byte_count);

  ExpectCtnSramWriteEnable();
  EXPECT_CALL(ctn_sram_, DataWrite(0xfff0, 4, HasBytes(flash_bytes_0)))
      .WillOnce(Return(kErrorOk));
  EXPECT_CALL(ctn_sram_, DataWrite(0xff00, 60, HasBytes(flash_bytes_1)))
      .WillOnce(Return(kErrorOk));
  ExpectCtnSramAllDisable();

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
  ExpectCtnSramChipErase(kErrorOk, kErrorOk);
  // Verify
  ExpectCtnSramEraseVerify(kErrorOk, kErrorOk);
  EXPECT_CALL(spi_device_, FlashStatusClear());
  // Program
  auto cmd = PageProgramCmd(816, 8);
  ExpectSpiCmd(cmd);
  ExpectSpiFlashStatusGet(true);

  std::vector<uint8_t> flash_bytes(cmd.payload,
                                   cmd.payload + cmd.payload_byte_count);

  ExpectCtnSramWriteEnable();
  EXPECT_CALL(ctn_sram_, DataWrite(816, 2, HasBytes(flash_bytes)))
      .WillOnce(Return(kErrorOk));
  ExpectCtnSramAllDisable();

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
  ExpectCtnSramChipErase(kErrorOk, kErrorOk);
  // Verify
  ExpectCtnSramEraseVerify(kErrorOk, kErrorOk);
  EXPECT_CALL(spi_device_, FlashStatusClear());
  // Program
  auto cmd = PageProgramCmd(0, 16);
  ExpectSpiCmd(cmd);
  ExpectSpiFlashStatusGet(true);

  std::vector<uint8_t> flash_bytes(cmd.payload,
                                   cmd.payload + cmd.payload_byte_count);

  ExpectCtnSramWriteEnable();
  EXPECT_CALL(ctn_sram_,
              DataWrite(cmd.address, cmd.payload_byte_count / sizeof(uint32_t),
                        HasBytes(flash_bytes)))
      .WillOnce(Return(kErrorOk));
  ExpectCtnSramAllDisable();

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
  ExpectCtnSramChipErase(kErrorOk, kErrorOk);
  // Verify
  ExpectCtnSramEraseVerify(kErrorOk, kErrorOk);
  EXPECT_CALL(spi_device_, FlashStatusClear());
  // Program
  auto cmd = PageProgramCmd(0, 16);
  ExpectSpiCmd(cmd);
  ExpectSpiFlashStatusGet(true);

  std::vector<uint8_t> flash_bytes(cmd.payload,
                                   cmd.payload + cmd.payload_byte_count);

  ExpectCtnSramWriteEnable();
  EXPECT_CALL(ctn_sram_,
              DataWrite(cmd.address, cmd.payload_byte_count / sizeof(uint32_t),
                        HasBytes(flash_bytes)))
      .WillOnce(Return(kErrorOk));
  ExpectCtnSramAllDisable();

  EXPECT_CALL(spi_device_, FlashStatusClear());
  // Chip erase
  ExpectSpiCmd(ChipEraseCmd());
  ExpectSpiFlashStatusGet(true);
  ExpectCtnSramChipErase(kErrorOk, kErrorOk);
  EXPECT_CALL(spi_device_, FlashStatusClear());
  // Sector erase
  ExpectSpiCmd(SectorEraseCmd(0));
  ExpectSpiFlashStatusGet(true);
  ExpectCtnSramSectorErase(kErrorOk, kErrorOk, 0);
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
  ExpectCtnSramChipErase(kErrorOk, kErrorOk);
  // Verify
  ExpectCtnSramEraseVerify(kErrorOk, kErrorOk);
  EXPECT_CALL(spi_device_, FlashStatusClear());
  // Erase with misaligned and aligned addresses
  ExpectSpiCmd(SectorEraseCmd(5));
  ExpectSpiFlashStatusGet(true);
  ExpectCtnSramSectorErase(kErrorOk, kErrorOk, 0);
  EXPECT_CALL(spi_device_, FlashStatusClear());

  ExpectSpiCmd(SectorEraseCmd(4096));
  ExpectSpiFlashStatusGet(true);
  ExpectCtnSramSectorErase(kErrorOk, kErrorOk, 4096);
  EXPECT_CALL(spi_device_, FlashStatusClear());

  ExpectSpiCmd(SectorEraseCmd(8195));
  ExpectSpiFlashStatusGet(true);
  ExpectCtnSramSectorErase(kErrorOk, kErrorOk, 8192);
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
  ExpectCtnSramChipErase(kErrorOk, kErrorOk);
  // Phase 1: Verify
  ExpectCtnSramEraseVerify(kErrorOk, kErrorOk);
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
  ExpectCtnSramChipErase(kErrorUnknown, kErrorOk);

  EXPECT_EQ(bootstrap(), kErrorUnknown);
}

TEST_F(BootstrapTest, EraseBank1Error) {
  ExpectBootstrapRequestCheck(true);
  EXPECT_CALL(spi_device_, Init());
  ExpectSpiCmd(ChipEraseCmd());
  ExpectSpiFlashStatusGet(true);
  ExpectCtnSramChipErase(kErrorOk, kErrorUnknown);

  EXPECT_EQ(bootstrap(), kErrorUnknown);
}

TEST_F(BootstrapTest, EraseVerifyBank0Error) {
  // Erase
  ExpectBootstrapRequestCheck(true);
  EXPECT_CALL(spi_device_, Init());
  ExpectSpiCmd(ChipEraseCmd());
  ExpectSpiFlashStatusGet(true);
  ExpectCtnSramChipErase(kErrorOk, kErrorOk);
  // Verify
  ExpectCtnSramEraseVerify(kErrorUnknown, kErrorOk);

  EXPECT_EQ(bootstrap(), kErrorUnknown);
}

TEST_F(BootstrapTest, EraseVerifyBank1Error) {
  // Erase
  ExpectBootstrapRequestCheck(true);
  EXPECT_CALL(spi_device_, Init());
  ExpectSpiCmd(ChipEraseCmd());
  ExpectSpiFlashStatusGet(true);
  ExpectCtnSramChipErase(kErrorOk, kErrorOk);
  // Verify
  ExpectCtnSramEraseVerify(kErrorOk, kErrorUnknown);

  EXPECT_EQ(bootstrap(), kErrorUnknown);
}

TEST_F(BootstrapTest, DataWriteError) {
  // Erase
  ExpectBootstrapRequestCheck(true);
  EXPECT_CALL(spi_device_, Init());
  ExpectSpiCmd(ChipEraseCmd());
  ExpectSpiFlashStatusGet(true);
  ExpectCtnSramChipErase(kErrorOk, kErrorOk);
  // Verify
  ExpectCtnSramEraseVerify(kErrorOk, kErrorOk);
  EXPECT_CALL(spi_device_, FlashStatusClear());
  // Program
  auto cmd = PageProgramCmd(0, 16);
  ExpectSpiCmd(cmd);
  ExpectSpiFlashStatusGet(true);

  std::vector<uint8_t> flash_bytes(cmd.payload,
                                   cmd.payload + cmd.payload_byte_count);

  ExpectCtnSramWriteEnable();
  EXPECT_CALL(ctn_sram_,
              DataWrite(cmd.address, cmd.payload_byte_count / sizeof(uint32_t),
                        HasBytes(flash_bytes)))
      .WillOnce(Return(kErrorUnknown));
  ExpectCtnSramAllDisable();

  EXPECT_EQ(bootstrap(), kErrorUnknown);
}

TEST_F(BootstrapTest, DataWriteErrorMisalignedAddr) {
  // Erase
  ExpectBootstrapRequestCheck(true);
  EXPECT_CALL(spi_device_, Init());
  ExpectSpiCmd(ChipEraseCmd());
  ExpectSpiFlashStatusGet(true);
  ExpectCtnSramChipErase(kErrorOk, kErrorOk);
  // Verify
  ExpectCtnSramEraseVerify(kErrorOk, kErrorOk);
  EXPECT_CALL(spi_device_, FlashStatusClear());
  // Program
  auto cmd = PageProgramCmd(0xf0, 16);
  ExpectSpiCmd(cmd);
  ExpectSpiFlashStatusGet(true);

  std::vector<uint8_t> flash_bytes(cmd.payload,
                                   cmd.payload + cmd.payload_byte_count);

  ExpectCtnSramWriteEnable();
  EXPECT_CALL(ctn_sram_, DataWrite(0xf0, 4, HasBytes(flash_bytes)))
      .WillOnce(Return(kErrorUnknown));
  ExpectCtnSramAllDisable();

  EXPECT_EQ(bootstrap(), kErrorUnknown);
}

TEST_F(BootstrapTest, BadProgramAddress) {
  // Erase
  ExpectBootstrapRequestCheck(true);
  EXPECT_CALL(spi_device_, Init());
  ExpectSpiCmd(ChipEraseCmd());
  ExpectSpiFlashStatusGet(true);
  ExpectCtnSramChipErase(kErrorOk, kErrorOk);
  // Verify
  ExpectCtnSramEraseVerify(kErrorOk, kErrorOk);
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
  ExpectCtnSramChipErase(kErrorOk, kErrorOk);
  // Verify
  ExpectCtnSramEraseVerify(kErrorOk, kErrorOk);
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
