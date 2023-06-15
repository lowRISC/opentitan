// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/bootstrap_unittest_util.h"

#include <stdint.h>
#include <string.h>

#include "sw/device/silicon_creator/lib/base/chip.h"

#include "flash_ctrl_regs.h"
#include "gpio_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"

bool operator==(flash_ctrl_perms_t lhs, flash_ctrl_perms_t rhs) {
  return memcmp(&lhs, &rhs, sizeof(flash_ctrl_perms_t)) == 0;
}

namespace bootstrap_unittest_util {

namespace {
using ::testing::DoAll;
using ::testing::NotNull;
using ::testing::Return;
using ::testing::SetArgPointee;
}  // namespace

void BootstrapTest::ExpectBootstrapRequestCheck(bool requested) {
  EXPECT_CALL(otp_,
              read32(OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_BOOTSTRAP_DIS_OFFSET))
      .WillOnce(Return(kHardenedBoolFalse));
  uint32_t pins = SW_STRAP_BOOTSTRAP;
  if (!requested) {
    pins = ~pins;
  }
  EXPECT_ABS_READ32(TOP_EARLGREY_GPIO_BASE_ADDR + GPIO_DATA_IN_REG_OFFSET,
                    pins);
}

void BootstrapTest::ExpectSpiCmd(spi_device_cmd_t cmd) {
  EXPECT_CALL(spi_device_, CmdGet(NotNull()))
      .WillOnce(DoAll(SetArgPointee<0>(cmd), Return(kErrorOk)));
}

void BootstrapTest::ExpectSpiFlashStatusGet(bool wel) {
  EXPECT_CALL(spi_device_, FlashStatusGet())
      .WillOnce(Return(wel << kSpiDeviceWelBit));
}

void BootstrapTest::ExpectFlashCtrlWriteEnable() {
  EXPECT_CALL(flash_ctrl_, DataDefaultPermsSet((flash_ctrl_perms_t){
                               .read = kMultiBitBool4False,
                               .write = kMultiBitBool4True,
                               .erase = kMultiBitBool4False,
                           }));
}

void BootstrapTest::ExpectFlashCtrlEraseEnable() {
  EXPECT_CALL(flash_ctrl_, DataDefaultPermsSet((flash_ctrl_perms_t){
                               .read = kMultiBitBool4False,
                               .write = kMultiBitBool4False,
                               .erase = kMultiBitBool4True,
                           }));
}

void BootstrapTest::ExpectFlashCtrlAllDisable() {
  EXPECT_CALL(flash_ctrl_, DataDefaultPermsSet((flash_ctrl_perms_t){
                               .read = kMultiBitBool4False,
                               .write = kMultiBitBool4False,
                               .erase = kMultiBitBool4False,
                           }));
}

void BootstrapTest::ExpectFlashCtrlChipErase(rom_error_t err0,
                                             rom_error_t err1) {
  EXPECT_CALL(flash_ctrl_, BankErasePermsSet(kHardenedBoolTrue));
  EXPECT_CALL(flash_ctrl_, DataErase(0, kFlashCtrlEraseTypeBank))
      .WillOnce(Return(err0));
  EXPECT_CALL(flash_ctrl_, DataErase(FLASH_CTRL_PARAM_BYTES_PER_BANK,
                                     kFlashCtrlEraseTypeBank))
      .WillOnce(Return(err1));
  EXPECT_CALL(flash_ctrl_, BankErasePermsSet(kHardenedBoolFalse));
}

void BootstrapTest::ExpectFlashCtrlSectorErase(rom_error_t err0,
                                               rom_error_t err1,
                                               uint32_t addr) {
  EXPECT_CALL(flash_ctrl_, DataDefaultPermsSet((flash_ctrl_perms_t){
                               .read = kMultiBitBool4False,
                               .write = kMultiBitBool4False,
                               .erase = kMultiBitBool4True,
                           }));
  EXPECT_CALL(flash_ctrl_, DataErase(addr, kFlashCtrlEraseTypePage))
      .WillOnce(Return(err0));
  EXPECT_CALL(flash_ctrl_, DataErase(addr + FLASH_CTRL_PARAM_BYTES_PER_PAGE,
                                     kFlashCtrlEraseTypePage))
      .WillOnce(Return(err1));
  ExpectFlashCtrlAllDisable();
}

void BootstrapTest::ExpectFlashCtrlEraseVerify(rom_error_t err0,
                                               rom_error_t err1) {
  EXPECT_CALL(flash_ctrl_, DataEraseVerify(0, kFlashCtrlEraseTypeBank))
      .WillOnce(Return(err0));
  EXPECT_CALL(flash_ctrl_, DataEraseVerify(FLASH_CTRL_PARAM_BYTES_PER_BANK,
                                           kFlashCtrlEraseTypeBank))
      .WillOnce(Return(err1));
}

spi_device_cmd_t ChipEraseCmd() {
  return {
      .opcode = kSpiDeviceOpcodeChipErase,
      .address = kSpiDeviceNoAddress,
      .payload_byte_count = 0,
      .payload = {},
  };
}

spi_device_cmd_t SectorEraseCmd(uint32_t address) {
  return {
      .opcode = kSpiDeviceOpcodeSectorErase,
      .address = address,
      .payload_byte_count = 0,
      .payload = {},
  };
}

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

}  // namespace bootstrap_unittest_util
