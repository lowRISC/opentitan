// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/bootstrap_unittest_util.h"

#include <stdint.h>
#include <string.h>

#include "sw/device/silicon_creator/lib/base/chip.h"
#include "sw/device/silicon_creator/lib/nvm_ctrl.h"

#ifndef HAS_RRAM_CTRL
#include "hw/top/flash_ctrl_regs.h"
#endif  // !HAS_RRAM_CTRL
#include "hw/top/gpio_regs.h"
#include "hw/top/otp_ctrl_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#ifndef HAS_RRAM_CTRL
bool operator==(flash_ctrl_perms_t lhs, flash_ctrl_perms_t rhs) {
  return memcmp(&lhs, &rhs, sizeof(flash_ctrl_perms_t)) == 0;
}
#endif  // !HAS_RRAM_CTRL

namespace bootstrap_unittest_util {

namespace {
using ::testing::_;
using ::testing::DoAll;
using ::testing::InSequence;
using ::testing::NotNull;
using ::testing::Return;
using ::testing::SetArgPointee;
#ifdef HAS_RRAM_CTRL
using ::rom_test::RramPerms;
#endif  // HAS_RRAM_CTRL
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
  EXPECT_CALL(spi_device_, CmdGet(NotNull(), true))
      .WillOnce(DoAll(SetArgPointee<0>(cmd), Return(kErrorOk)));
}

void BootstrapTest::ExpectSpiFlashStatusGet(bool wel) {
  EXPECT_CALL(spi_device_, FlashStatusGet())
      .WillOnce(Return(wel << kSpiDeviceWelBit));
}

void BootstrapTest::ExpectFlashCtrlWriteEnable() {
#ifdef HAS_RRAM_CTRL
  // Unlike flash, RRAM's memory protection also gates the read path used
  // internally by a read-modify-write of unaligned partial granules, so
  // `nvm_ctrl_page_program()` enables read in addition to write (see
  // nvm_ctrl.c).
  EXPECT_CALL(flash_ctrl_, DataDefaultPermsSet(RramPerms(kMultiBitBool4True,
                                                         kMultiBitBool4True)));
#else
  EXPECT_CALL(flash_ctrl_, DataDefaultPermsSet((flash_ctrl_perms_t){
                               .read = kMultiBitBool4False,
                               .write = kMultiBitBool4True,
                               .erase = kMultiBitBool4False,
                           }));
#endif  // HAS_RRAM_CTRL
}

void BootstrapTest::ExpectFlashCtrlEraseEnable() {
#ifdef HAS_RRAM_CTRL
  // RRAM has no separate erase permission; `nvm_ctrl_sector_erase()`/
  // `nvm_ctrl_chip_erase()` enable the same read+write pair as page-program
  // (see nvm_ctrl.c). Not currently exercised by any test in this file.
  EXPECT_CALL(flash_ctrl_, DataDefaultPermsSet(RramPerms(kMultiBitBool4True,
                                                         kMultiBitBool4True)));
#else
  EXPECT_CALL(flash_ctrl_, DataDefaultPermsSet((flash_ctrl_perms_t){
                               .read = kMultiBitBool4False,
                               .write = kMultiBitBool4False,
                               .erase = kMultiBitBool4True,
                           }));
#endif  // HAS_RRAM_CTRL
}

void BootstrapTest::ExpectFlashCtrlAllDisable() {
#ifdef HAS_RRAM_CTRL
  EXPECT_CALL(flash_ctrl_, DataDefaultPermsSet(RramPerms(kMultiBitBool4False,
                                                         kMultiBitBool4False)));
#else
  EXPECT_CALL(flash_ctrl_, DataDefaultPermsSet((flash_ctrl_perms_t){
                               .read = kMultiBitBool4False,
                               .write = kMultiBitBool4False,
                               .erase = kMultiBitBool4False,
                           }));
#endif  // HAS_RRAM_CTRL
}

void BootstrapTest::ExpectFlashCtrlChipErase(rom_error_t err0,
                                             rom_error_t err1) {
#ifdef HAS_RRAM_CTRL
  // RRAM has no bank-erase primitive: `nvm_ctrl_chip_erase()` instead loops
  // over every usable data page (`NVM_USABLE_DATA_SIZE_BYTES /
  // NVM_BYTES_PER_PAGE` of them), writing each with a `DataWrite` of an
  // all-0xFF page, and stops at the first error. There's no real "bank"
  // boundary to target on RRAM, so -- to preserve this helper's existing
  // two-error-code call sites -- `err0` models the loop's first call
  // failing (immediate short-circuit) and `err1` models its last call
  // failing (every other page succeeds first).
  enum { kNumPages = NVM_USABLE_DATA_SIZE_BYTES / NVM_BYTES_PER_PAGE };
  EXPECT_CALL(flash_ctrl_, DataDefaultPermsSet(RramPerms(kMultiBitBool4True,
                                                         kMultiBitBool4True)));
  if (err0 != kErrorOk) {
    EXPECT_CALL(flash_ctrl_, DataWrite(_, _, _)).WillOnce(Return(err0));
  } else if (err1 != kErrorOk) {
    InSequence seq;
    EXPECT_CALL(flash_ctrl_, DataWrite(_, _, _))
        .Times(kNumPages - 1)
        .WillRepeatedly(Return(kErrorOk));
    EXPECT_CALL(flash_ctrl_, DataWrite(_, _, _)).WillOnce(Return(err1));
  } else {
    EXPECT_CALL(flash_ctrl_, DataWrite(_, _, _))
        .Times(kNumPages)
        .WillRepeatedly(Return(kErrorOk));
  }
  EXPECT_CALL(flash_ctrl_, DataDefaultPermsSet(RramPerms(kMultiBitBool4False,
                                                         kMultiBitBool4False)));
#else
  EXPECT_CALL(flash_ctrl_, BankErasePermsSet(kHardenedBoolTrue));
  EXPECT_CALL(flash_ctrl_, DataErase(0, kFlashCtrlEraseTypeBank))
      .WillOnce(Return(err0));
  EXPECT_CALL(flash_ctrl_, DataErase(FLASH_CTRL_PARAM_BYTES_PER_BANK,
                                     kFlashCtrlEraseTypeBank))
      .WillOnce(Return(err1));
  EXPECT_CALL(flash_ctrl_, BankErasePermsSet(kHardenedBoolFalse));
#endif  // HAS_RRAM_CTRL
}

void BootstrapTest::ExpectFlashCtrlSectorErase(rom_error_t err0,
                                               rom_error_t err1,
                                               uint32_t addr) {
#ifdef HAS_RRAM_CTRL
  // RRAM's `nvm_ctrl_sector_erase()` erases a fixed 4 KiB region (already
  // aligned by the caller, same as the flash branch below) as
  // `kSectorSizeBytes / NVM_BYTES_PER_PAGE` individual page `DataWrite`s --
  // see the RRAM note on `ExpectFlashCtrlChipErase()` above for why
  // `err0`/`err1` model the first/last call rather than "page 0"/"page 1".
  enum {
    kSectorSizeBytes = 4096,
    kSectorPages = kSectorSizeBytes / NVM_BYTES_PER_PAGE,
    kPageWords = NVM_BYTES_PER_PAGE / sizeof(uint32_t),
  };
  EXPECT_CALL(flash_ctrl_, DataDefaultPermsSet(RramPerms(kMultiBitBool4True,
                                                         kMultiBitBool4True)));
  if (err0 != kErrorOk) {
    EXPECT_CALL(flash_ctrl_, DataWrite(addr, kPageWords, _))
        .WillOnce(Return(err0));
  } else {
    for (uint32_t i = 0; i < kSectorPages; ++i) {
      rom_error_t err = (i == kSectorPages - 1) ? err1 : kErrorOk;
      EXPECT_CALL(flash_ctrl_,
                  DataWrite(addr + i * NVM_BYTES_PER_PAGE, kPageWords, _))
          .WillOnce(Return(err));
    }
  }
  ExpectFlashCtrlAllDisable();
#else
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
#endif  // HAS_RRAM_CTRL
}

void BootstrapTest::ExpectFlashCtrlEraseVerify(rom_error_t err0,
                                               rom_error_t err1) {
#ifdef HAS_RRAM_CTRL
  // `nvm_ctrl_chip_erase_verify()` is a hardcoded `return kErrorOk;` on RRAM
  // (there's no separate verify-read step), so there is no driver call to
  // set an expectation on.
  (void)err0;
  (void)err1;
#else
  EXPECT_CALL(flash_ctrl_, DataEraseVerify(0, kFlashCtrlEraseTypeBank))
      .WillOnce(Return(err0));
  EXPECT_CALL(flash_ctrl_, DataEraseVerify(FLASH_CTRL_PARAM_BYTES_PER_BANK,
                                           kFlashCtrlEraseTypeBank))
      .WillOnce(Return(err1));
#endif  // HAS_RRAM_CTRL
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
