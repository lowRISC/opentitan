// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/ownership/owner_block.h"

#include <stdint.h>
#include <tuple>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/testing/binary_blob.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/drivers/mock_flash_ctrl.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/ownership/datatypes.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace {
#include "sw/device/silicon_creator/lib/ownership/testdata/basic_owner_testdata.h"

using rom_test::FlashCfg;
using rom_test::FlashPerms;
using rom_test::MockFlashCtrl;
using ::testing::_;
using ::testing::Return;
using ::testutil::BinaryBlob;

class OwnerBlockTest : public rom_test::RomTest {
 protected:
  MockFlashCtrl flash_ctrl_;
  flash_ctrl_cfg_t default_config = {
      .scrambling = kMultiBitBool4False,
      .ecc = kMultiBitBool4False,
      .he = kMultiBitBool4False,
  };

  void SetUp() override {
    ON_CALL(flash_ctrl_, DataDefaultCfgGet)
        .WillByDefault(Return(default_config));
  }
};

// clang-format off
// Create and "encrypt" the `access` word of a flash region config.
#define FLASH_ACCESS(index, read, program, erase, pwp, lock) ( \
    ( \
      bitfield_field32_write(0, FLASH_CONFIG_READ, read ? kMultiBitBool4True : kMultiBitBool4False) | \
      bitfield_field32_write(0, FLASH_CONFIG_PROGRAM, program ? kMultiBitBool4True : kMultiBitBool4False) | \
      bitfield_field32_write(0, FLASH_CONFIG_ERASE, erase ? kMultiBitBool4True : kMultiBitBool4False) | \
      bitfield_field32_write(0, FLASH_CONFIG_PROTECT_WHEN_PRIMARY, pwp ? kMultiBitBool4True : kMultiBitBool4False) | \
      bitfield_field32_write(0, FLASH_CONFIG_LOCK, lock ? kMultiBitBool4True : kMultiBitBool4False) \
    ) ^ (0x11111111 * index) \
  )

// Create and "encrypt" the `properties` word of a flash region config.
#define FLASH_PROP(index, scramble, ecc, he) ( \
    ( \
      bitfield_field32_write(0, FLASH_CONFIG_SCRAMBLE, scramble ? kMultiBitBool4True : kMultiBitBool4False) | \
      bitfield_field32_write(0, FLASH_CONFIG_ECC, ecc ? kMultiBitBool4True : kMultiBitBool4False) | \
      bitfield_field32_write(0, FLASH_CONFIG_HIGH_ENDURANCE, he ? kMultiBitBool4True : kMultiBitBool4False) \
    ) ^ (0x11111111 * index) \
  )
// clang-format on

const owner_flash_config_t simple_flash_config = {
    .header =
        {
            .tag = kTlvTagFlashConfig,
            .length =
                sizeof(owner_flash_config_t) + 4 * sizeof(owner_flash_region_t),
        },
    .config =
        {
            {
                // SideA FIRMWARE.
                .start = 32,
                .size = 192,
                .access = FLASH_ACCESS(
                    /*index=*/0,
                    /*read=*/true,
                    /*program=*/true,
                    /*erase=*/true,
                    /*pwp=*/true,
                    /*lock=*/false),
                .properties = FLASH_PROP(
                    /*index=*/0,
                    /*scramble=*/true,
                    /*ecc=*/true,
                    /*he=*/false),
            },
            {
                // SideA Filesystem.
                .start = 224,
                .size = 32,
                .access = FLASH_ACCESS(
                    /*index=*/1,
                    /*read=*/true,
                    /*program=*/true,
                    /*erase=*/true,
                    /*pwp=*/false,
                    /*lock=*/false),
                .properties = FLASH_PROP(
                    /*index=*/1,
                    /*scramble=*/false,
                    /*ecc=*/false,
                    /*he=*/true),
            },
            {
                // SideB FIRMWARE.
                .start = 256 + 32,
                .size = 192,
                .access = FLASH_ACCESS(
                    /*index=*/2,
                    /*read=*/true,
                    /*program=*/true,
                    /*erase=*/true,
                    /*pwp=*/true,
                    /*lock=*/false),
                .properties = FLASH_PROP(
                    /*index=*/2,
                    /*scramble=*/true,
                    /*ecc=*/true,
                    /*he=*/false),
            },
            {
                // SideB Filesystem.
                .start = 256 + 224,
                .size = 32,
                .access = FLASH_ACCESS(
                    /*index=*/3,
                    /*read=*/true,
                    /*program=*/true,
                    /*erase=*/true,
                    /*pwp=*/false,
                    /*lock=*/false),
                .properties = FLASH_PROP(
                    /*index=*/3,
                    /*scramble=*/false,
                    /*ecc=*/false,
                    /*he=*/true),
            },
        },
};

const owner_flash_config_t flash_config_contains_rom_ext = {
    .header =
        {
            .tag = kTlvTagFlashConfig,
            .length =
                sizeof(owner_flash_config_t) + 2 * sizeof(owner_flash_region_t),
        },
    .config =
        {
            {
                // SideA ROM_EXT.
                .start = 0,
                .size = 32,
                .access = FLASH_ACCESS(
                    /*index=*/0,
                    /*read=*/true,
                    /*program=*/true,
                    /*erase=*/true,
                    /*pwp=*/true,
                    /*lock=*/false),
                .properties = FLASH_PROP(
                    /*index=*/0,
                    /*scramble=*/false,
                    /*ecc=*/false,
                    /*he=*/false),

            },
            {
                // SideB ROM_EXT.
                .start = 256 + 0,
                .size = 32,
                .access = FLASH_ACCESS(
                    /*index=*/3,
                    /*read=*/true,
                    /*program=*/true,
                    /*erase=*/true,
                    /*pwp=*/true,
                    /*lock=*/false),
                .properties = FLASH_PROP(
                    /*index=*/3,
                    /*scramble=*/false,
                    /*ecc=*/false,
                    /*he=*/false),
            },
        },
};

const owner_flash_info_config_t info_config = {
    .header =
        {
            .tag = kTlvTagInfoConfig,
            .length =
                sizeof(owner_flash_config_t) + 2 * sizeof(owner_flash_region_t),
        },
    .config =
        {
            {
                // User page
                .bank = 0,
                .page = 6,
                .access = FLASH_ACCESS(
                    /*index=*/0,
                    /*read=*/true,
                    /*program=*/true,
                    /*erase=*/true,
                    /*pwp=*/false,
                    /*lock=*/false),
                .properties = FLASH_PROP(
                    /*index=*/0,
                    /*scramble=*/false,
                    /*ecc=*/false,
                    /*he=*/true),

            },
            {
                // Disallowed page
                .bank = 0,
                .page = 9,
                .access = FLASH_ACCESS(
                    /*index=*/1,
                    /*read=*/true,
                    /*program=*/true,
                    /*erase=*/true,
                    /*pwp=*/false,
                    /*lock=*/false),
                .properties = FLASH_PROP(
                    /*index=*/1,
                    /*scramble=*/false,
                    /*ecc=*/false,
                    /*he=*/false),
            },

        },
};

TEST_F(OwnerBlockTest, FlashConfigApplyBadRomExt) {
  // There are no expectations because `owner_block_flash_apply` will ignore
  // regions that match the ROM_EXT.  This is intentional so pre-existing owner
  // configs that cover the ROM_EXT won't result in an error and boot-loop the
  // chip.
  uint32_t mp_index = 0;
  rom_error_t error =
      owner_block_flash_apply(&flash_config_contains_rom_ext, kBootSlotA,
                              /*owner_lockdown=*/0, &mp_index);
  EXPECT_EQ(error, kErrorOk);
}

// Tests that the flash parameters get applied for side A.
TEST_F(OwnerBlockTest, FlashConfigApplySideA) {
  // The ROM_EXT always uses regions 0-1 to protect itself,  The items in
  // the flash config always get programmed in order starting at index 2.
  EXPECT_CALL(
      flash_ctrl_,
      DataRegionProtect(
          2, 32, 192,
          FlashPerms(kMultiBitBool4True, kMultiBitBool4True,
                     kMultiBitBool4True),
          FlashCfg(kMultiBitBool4True, kMultiBitBool4True, kMultiBitBool4False),
          kHardenedBoolFalse));
  EXPECT_CALL(
      flash_ctrl_,
      DataRegionProtect(3, 224, 32,
                        FlashPerms(kMultiBitBool4True, kMultiBitBool4True,
                                   kMultiBitBool4True),
                        FlashCfg(kMultiBitBool4False, kMultiBitBool4False,
                                 kMultiBitBool4True),
                        kHardenedBoolFalse));

  uint32_t mp_index = 0;
  rom_error_t error = owner_block_flash_apply(&simple_flash_config, kBootSlotA,
                                              /*owner_lockdown=*/0, &mp_index);
  EXPECT_EQ(error, kErrorOk);
}

// Tests that the flash parameters get applied for side A and the
// ProtectWhenActive disables erase and program on the ROM_EXT and FIRMWARE
// regions.
TEST_F(OwnerBlockTest, FlashConfigApplySideA_Active) {
  // The ROM_EXT always uses regions 0-1 to protect itself,  The items in
  // the flash config always get programmed in order starting at index 2.
  EXPECT_CALL(
      flash_ctrl_,
      DataRegionProtect(
          2, 32, 192,
          FlashPerms(kMultiBitBool4True, kMultiBitBool4False,
                     kMultiBitBool4False),
          FlashCfg(kMultiBitBool4True, kMultiBitBool4True, kMultiBitBool4False),
          kHardenedBoolFalse));
  EXPECT_CALL(
      flash_ctrl_,
      DataRegionProtect(3, 224, 32,
                        FlashPerms(kMultiBitBool4True, kMultiBitBool4True,
                                   kMultiBitBool4True),
                        FlashCfg(kMultiBitBool4False, kMultiBitBool4False,
                                 kMultiBitBool4True),
                        kHardenedBoolFalse));

  uint32_t mp_index = 0;
  rom_error_t error =
      owner_block_flash_apply(&simple_flash_config, kBootSlotA,
                              /*owner_lockdown=*/kBootSlotA, &mp_index);
  EXPECT_EQ(error, kErrorOk);
}

// Tests that the flash parameters get applied for side B when B is not the
// active slot.  Check that ProtectWhenActive does not change the write/erase
// permissions for slot B.
TEST_F(OwnerBlockTest, FlashConfigApplySideB_NotActive) {
  // The ROM_EXT always uses regions 0-1 to protect itself,  The items in
  // the flash config always get programmed in order starting at index 2.
  EXPECT_CALL(
      flash_ctrl_,
      DataRegionProtect(
          2, 256 + 32, 192,
          FlashPerms(kMultiBitBool4True, kMultiBitBool4True,
                     kMultiBitBool4True),
          FlashCfg(kMultiBitBool4True, kMultiBitBool4True, kMultiBitBool4False),
          kHardenedBoolFalse));
  EXPECT_CALL(
      flash_ctrl_,
      DataRegionProtect(3, 256 + 224, 32,
                        FlashPerms(kMultiBitBool4True, kMultiBitBool4True,
                                   kMultiBitBool4True),
                        FlashCfg(kMultiBitBool4False, kMultiBitBool4False,
                                 kMultiBitBool4True),
                        kHardenedBoolFalse));

  uint32_t mp_index = 0;
  rom_error_t error =
      owner_block_flash_apply(&simple_flash_config, kBootSlotB,
                              /*owner_lockdown=*/kBootSlotA, &mp_index);
  EXPECT_EQ(error, kErrorOk);
}

const owner_flash_config_t legacy_flash_config = {
    .header =
        {
            .tag = kTlvTagFlashConfig,
            .length =
                sizeof(owner_flash_config_t) + 8 * sizeof(owner_flash_region_t),
        },
    .config =
        {
            {
                // SideA ROM_EXT.  This configuration should be skipped
                // by flash_ apply.
                .start = 0,
                .size = 32,
                .access = FLASH_ACCESS(
                    /*index=*/0,
                    /*read=*/true,
                    /*program=*/true,
                    /*erase=*/true,
                    /*pwp=*/true,
                    /*lock=*/false),
                .properties = FLASH_PROP(
                    /*index=*/0,
                    /*scramble=*/false,
                    /*ecc=*/false,
                    /*he=*/false),

            },
            {
                // SideA FIRMWARE.
                .start = 32,
                .size = 192,
                .access = FLASH_ACCESS(
                    /*index=*/1,
                    /*read=*/true,
                    /*program=*/true,
                    /*erase=*/true,
                    /*pwp=*/true,
                    /*lock=*/false),
                .properties = FLASH_PROP(
                    /*index=*/1,
                    /*scramble=*/true,
                    /*ecc=*/true,
                    /*he=*/false),
            },
            {
                // SideA Filesystem.
                .start = 224,
                .size = 31,
                .access = FLASH_ACCESS(
                    /*index=*/2,
                    /*read=*/true,
                    /*program=*/true,
                    /*erase=*/true,
                    /*pwp=*/false,
                    /*lock=*/false),
                .properties = FLASH_PROP(
                    /*index=*/2,
                    /*scramble=*/false,
                    /*ecc=*/false,
                    /*he=*/true),
            },
            {
                // SideA ROM_EXT.  This configuration should be skipped
                // by flash_ apply.
                .start = 256 + 0,
                .size = 32,
                .access = FLASH_ACCESS(
                    /*index=*/3,
                    /*read=*/true,
                    /*program=*/true,
                    /*erase=*/true,
                    /*pwp=*/true,
                    /*lock=*/false),
                .properties = FLASH_PROP(
                    /*index=*/3,
                    /*scramble=*/false,
                    /*ecc=*/false,
                    /*he=*/false),
            },
            {
                // SideB FIRMWARE.
                .start = 256 + 32,
                .size = 192,
                .access = FLASH_ACCESS(
                    /*index=*/4,
                    /*read=*/true,
                    /*program=*/true,
                    /*erase=*/true,
                    /*pwp=*/true,
                    /*lock=*/false),
                .properties = FLASH_PROP(
                    /*index=*/4,
                    /*scramble=*/true,
                    /*ecc=*/true,
                    /*he=*/false),
            },
            {
                // SideB Filesystem.
                .start = 256 + 224,
                .size = 31,
                .access = FLASH_ACCESS(
                    /*index=*/5,
                    /*read=*/true,
                    /*program=*/true,
                    /*erase=*/true,
                    /*pwp=*/false,
                    /*lock=*/false),
                .properties = FLASH_PROP(
                    /*index=*/5,
                    /*scramble=*/false,
                    /*ecc=*/false,
                    /*he=*/true),
            },
            {
                // SideA Reserved last page.
                .start = 255,
                .size = 1,
                .access = FLASH_ACCESS(
                    /*index=*/6,
                    /*read=*/true,
                    /*program=*/true,
                    /*erase=*/true,
                    /*pwp=*/false,
                    /*lock=*/false),
                .properties = FLASH_PROP(
                    /*index=*/6,
                    /*scramble=*/true,
                    /*ecc=*/true,
                    /*he=*/false),
            },
            {
                // SideB Reserved last page.
                .start = 511,
                .size = 1,
                .access = FLASH_ACCESS(
                    /*index=*/7,
                    /*read=*/true,
                    /*program=*/true,
                    /*erase=*/true,
                    /*pwp=*/false,
                    /*lock=*/false),
                .properties = FLASH_PROP(
                    /*index=*/7,
                    /*scramble=*/true,
                    /*ecc=*/true,
                    /*he=*/false),
            },

        },
};

// Tests that the flash parameters get applied for side B when B is not the
// active slot.  Check that ProtectWhenActive does not change the write/erase
// permissions for slot B.
TEST_F(OwnerBlockTest, FlashConfigApplyLegacy) {
  // The ROM_EXT always uses regions 0-1 to protect itself,  The items in
  // the flash config always get programmed in order starting at index 2.

  // We should not see the ROM_EXT regions from the `legacy_flash_config`.
  // We should see the rest of the regions in order.

  // The SideA Firmware region has "protect when active" set, so the erase
  // and program permissions should be false.
  EXPECT_CALL(
      flash_ctrl_,
      DataRegionProtect(
          2, 32, 192,
          FlashPerms(kMultiBitBool4True, kMultiBitBool4False,
                     kMultiBitBool4False),
          FlashCfg(kMultiBitBool4True, kMultiBitBool4True, kMultiBitBool4False),
          kHardenedBoolFalse));
  EXPECT_CALL(
      flash_ctrl_,
      DataRegionProtect(3, 224, 31,
                        FlashPerms(kMultiBitBool4True, kMultiBitBool4True,
                                   kMultiBitBool4True),
                        FlashCfg(kMultiBitBool4False, kMultiBitBool4False,
                                 kMultiBitBool4True),
                        kHardenedBoolFalse));
  // The SideA reserved last page is out-of-order with the rest of the SideA
  // entries.  This is ok, and it should land in the next mp_region register.
  EXPECT_CALL(
      flash_ctrl_,
      DataRegionProtect(
          4, 255, 1,
          FlashPerms(kMultiBitBool4True, kMultiBitBool4True,
                     kMultiBitBool4True),
          FlashCfg(kMultiBitBool4True, kMultiBitBool4True, kMultiBitBool4False),
          kHardenedBoolFalse));

  // The SideB Firmware region has "protect when active" set, but it isn't
  // the active side, so the erase and program permissions should be true.
  EXPECT_CALL(
      flash_ctrl_,
      DataRegionProtect(
          5, 256 + 32, 192,
          FlashPerms(kMultiBitBool4True, kMultiBitBool4True,
                     kMultiBitBool4True),
          FlashCfg(kMultiBitBool4True, kMultiBitBool4True, kMultiBitBool4False),
          kHardenedBoolFalse));
  EXPECT_CALL(
      flash_ctrl_,
      DataRegionProtect(6, 256 + 224, 31,
                        FlashPerms(kMultiBitBool4True, kMultiBitBool4True,
                                   kMultiBitBool4True),
                        FlashCfg(kMultiBitBool4False, kMultiBitBool4False,
                                 kMultiBitBool4True),
                        kHardenedBoolFalse));
  // The SideB reserved last page is out-of-order with the rest of the SideB
  // entries.  This is ok, and it should land in the next mp_region register.
  EXPECT_CALL(
      flash_ctrl_,
      DataRegionProtect(
          7, 511, 1,
          FlashPerms(kMultiBitBool4True, kMultiBitBool4True,
                     kMultiBitBool4True),
          FlashCfg(kMultiBitBool4True, kMultiBitBool4True, kMultiBitBool4False),
          kHardenedBoolFalse));

  uint32_t mp_index = 0;
  rom_error_t error =
      owner_block_flash_apply(&legacy_flash_config, kBootSlotA,
                              /*owner_lockdown=*/kBootSlotA, &mp_index);
  EXPECT_EQ(error, kErrorOk);
  error = owner_block_flash_apply(&legacy_flash_config, kBootSlotB,
                                  /*owner_lockdown=*/kBootSlotA, &mp_index);
  EXPECT_EQ(error, kErrorOk);
}

TEST_F(OwnerBlockTest, FlashInfoApply) {
  EXPECT_CALL(flash_ctrl_, InfoType0ParamsBuild(0, 6, _))
      .WillOnce(Return(kErrorOk));
  EXPECT_CALL(flash_ctrl_,
              InfoCfgSet(_, FlashCfg(kMultiBitBool4False, kMultiBitBool4False,
                                     kMultiBitBool4True)));
  EXPECT_CALL(flash_ctrl_,
              InfoPermsSet(_, FlashPerms(kMultiBitBool4True, kMultiBitBool4True,
                                         kMultiBitBool4True)));

  rom_error_t error = owner_block_info_apply(&info_config);
  EXPECT_EQ(error, kErrorOk);
}

TEST_F(OwnerBlockTest, ParseBlock) {
  BinaryBlob<owner_block_t> block(basic_owner, sizeof(basic_owner));
  owner_config_t config;
  owner_application_keyring_t keyring{};

  EXPECT_CALL(flash_ctrl_, DataDefaultCfgGet)
      .WillRepeatedly(Return(default_config));
  rom_error_t error = owner_block_parse(
      block.get(), /*check_only=*/kHardenedBoolFalse, &config, &keyring);
  EXPECT_EQ(error, kErrorOk);
  EXPECT_EQ(config.sram_exec, kOwnerSramExecModeDisabledLocked);
  EXPECT_EQ(config.flash->header.tag, kTlvTagFlashConfig);
  EXPECT_EQ(config.info->header.tag, kTlvTagInfoConfig);
  EXPECT_EQ(config.rescue->header.tag, kTlvTagRescueConfig);
  EXPECT_EQ(config.isfb->header.tag, kTlvTagIntegrationSpecificFirmwareBinding);
  EXPECT_EQ(keyring.length, 1);
  EXPECT_EQ(keyring.key[0]->header.tag, kTlvTagApplicationKey);
}

TEST_F(OwnerBlockTest, ParseBlockBadHeaderLength) {
  BinaryBlob<owner_block_t> block(basic_owner, sizeof(basic_owner));
  // Rewrite the header length to a bad value
  block.Seek(offsetof(owner_block_t, header.length)).Write(12345);
  owner_config_t config;
  owner_application_keyring_t keyring{};
  rom_error_t error = owner_block_parse(
      block.get(), /*check_only=*/kHardenedBoolFalse, &config, &keyring);
  EXPECT_EQ(error, kErrorOwnershipInvalidTagLength);
}

TEST_F(OwnerBlockTest, ParseBlockBadHeaderTag) {
  BinaryBlob<owner_block_t> block(basic_owner, sizeof(basic_owner));
  // Rewrite the header tag from `OWNR` to `AAAA`.
  block.Seek(offsetof(owner_block_t, header.tag)).Write(0x41414141);
  owner_config_t config;
  owner_application_keyring_t keyring{};
  rom_error_t error = owner_block_parse(
      block.get(), /*check_only=*/kHardenedBoolFalse, &config, &keyring);
  EXPECT_EQ(error, kErrorOwnershipInvalidTag);
}

TEST_F(OwnerBlockTest, ParseBlockUnknownTag) {
  EXPECT_CALL(flash_ctrl_, DataDefaultCfgGet)
      .WillRepeatedly(Return(default_config));
  BinaryBlob<owner_block_t> block(basic_owner, sizeof(basic_owner));
  // Write an unknown header of {tag="AAAA", len=0x40} after the RESQ config.
  tlv_header_t rescue = block.Find(kTlvTagRescueConfig).Read<tlv_header_t>();
  block.Seek(rescue.length - sizeof(tlv_header_t))
      .Write(0x41414141)
      .Write(0x40);
  owner_config_t config;
  owner_application_keyring_t keyring{};

  rom_error_t error = owner_block_parse(
      block.get(), /*check_only=*/kHardenedBoolFalse, &config, &keyring);
  EXPECT_EQ(error, kErrorOwnershipInvalidTag);
}

TEST_F(OwnerBlockTest, ParseBlockBadLength) {
  BinaryBlob<owner_block_t> block(basic_owner, sizeof(basic_owner));
  owner_config_t config;
  owner_application_keyring_t keyring{};
  EXPECT_CALL(flash_ctrl_, DataDefaultCfgGet)
      .WillRepeatedly(Return(default_config));

  // Rewrite the RESQ block length to overflow the TLV region.
  block.Find(kTlvTagRescueConfig)
      .Seek(offsetof(tlv_header_t, length))
      .Write(uint16_t(0x600));
  rom_error_t error = owner_block_parse(
      block.get(), /*check_only=*/kHardenedBoolFalse, &config, &keyring);
  EXPECT_EQ(error, kErrorOwnershipInvalidTagLength);

  // Rewrite the RESQ block length to be too short.
  block.Reset()
      .Find(kTlvTagRescueConfig)
      .Seek(offsetof(tlv_header_t, length))
      .Write(uint16_t(0x4));
  error = owner_block_parse(block.get(), /*check_only=*/kHardenedBoolFalse,
                            &config, &keyring);
  EXPECT_EQ(error, kErrorOwnershipInvalidTagLength);

  // Rewrite the RESQ block length to not be a multiple of 4.
  block.Reset()
      .Find(kTlvTagRescueConfig)
      .Seek(offsetof(tlv_header_t, length))
      .Write(uint16_t(0x21));
  error = owner_block_parse(block.get(), /*check_only=*/kHardenedBoolFalse,
                            &config, &keyring);
  EXPECT_EQ(error, kErrorOwnershipInvalidTagLength);
}

TEST_F(OwnerBlockTest, ParseBlockDupFlash) {
  EXPECT_CALL(flash_ctrl_, DataDefaultCfgGet)
      .WillRepeatedly(Return(default_config));
  BinaryBlob<owner_block_t> block(basic_owner, sizeof(basic_owner));
  // Rewrite the RESQ tag as a FLSH tag to test duplicate detection.
  block.Find(kTlvTagRescueConfig).Write(kTlvTagFlashConfig);
  owner_config_t config;
  owner_application_keyring_t keyring{};
  rom_error_t error = owner_block_parse(
      block.get(), /*check_only=*/kHardenedBoolFalse, &config, &keyring);
  EXPECT_EQ(error, kErrorOwnershipDuplicateItem);
}

TEST_F(OwnerBlockTest, ParseBlockDupInfo) {
  EXPECT_CALL(flash_ctrl_, DataDefaultCfgGet)
      .WillRepeatedly(Return(default_config));
  BinaryBlob<owner_block_t> block(basic_owner, sizeof(basic_owner));
  // Rewrite the RESQ tag as an INFO tag to test duplicate detection.
  block.Find(kTlvTagRescueConfig).Write(kTlvTagInfoConfig);
  owner_config_t config;
  owner_application_keyring_t keyring{};
  rom_error_t error = owner_block_parse(
      block.get(), /*check_only=*/kHardenedBoolFalse, &config, &keyring);
  EXPECT_EQ(error, kErrorOwnershipDuplicateItem);
}

TEST_F(OwnerBlockTest, ParseBlockDupRescue) {
  BinaryBlob<owner_block_t> block(basic_owner, sizeof(basic_owner));
  // Rewrite the FLSH tag as a RESQ tag to test duplicate detection.
  block.Find(kTlvTagFlashConfig).Write(kTlvTagRescueConfig);
  owner_config_t config;
  owner_application_keyring_t keyring{};
  rom_error_t error = owner_block_parse(
      block.get(), /*check_only=*/kHardenedBoolFalse, &config, &keyring);
  EXPECT_EQ(error, kErrorOwnershipDuplicateItem);
}

TEST_F(OwnerBlockTest, ParseBlockDupIsfb) {
  EXPECT_CALL(flash_ctrl_, DataDefaultCfgGet)
      .WillRepeatedly(Return(default_config));
  BinaryBlob<owner_block_t> block(basic_owner, sizeof(basic_owner));
  // Rewrite the RESQ tag as an ISFB tag to test duplicate detection.
  block.Find(kTlvTagRescueConfig)
      .Write(kTlvTagIntegrationSpecificFirmwareBinding);
  owner_config_t config;
  owner_application_keyring_t keyring{};
  rom_error_t error = owner_block_parse(
      block.get(), /*check_only=*/kHardenedBoolFalse, &config, &keyring);
  EXPECT_EQ(error, kErrorOwnershipDuplicateItem);
}

const owner_isfb_config_t isfb_config_bad_page = {
    .header =
        {
            .tag = kTlvTagIntegrationSpecificFirmwareBinding,
            .length = sizeof(owner_isfb_config_t),
        },
    .bank = 0,
    // Invalid page. Page 0 is reserved by the Silicon Creator.
    .page = 0,
    .product_words = 4,
};

const owner_isfb_config_t isfb_config_bad_product_word_count = {
    .header =
        {
            .tag = kTlvTagIntegrationSpecificFirmwareBinding,
            .length = sizeof(owner_isfb_config_t),
        },
    .bank = 0,
    .page = 5,
    // Invalid product word count > 256.
    .product_words = 257,
};

struct IsfbError {
  owner_isfb_config_t config;
  rom_error_t expect;
};

class OwnerBlockBadIsfbTest : public OwnerBlockTest,
                              public testing::WithParamInterface<IsfbError> {};

TEST_P(OwnerBlockBadIsfbTest, ParseBlockBadIsfb) {
  IsfbError param = GetParam();
  rom_error_t error = owner_isfb_config_check(&param.config);
  EXPECT_EQ(error, param.expect);
}

INSTANTIATE_TEST_SUITE_P(
    AllCases, OwnerBlockBadIsfbTest,
    testing::Values(IsfbError{isfb_config_bad_page, kErrorOwnershipISFBPage},
                    IsfbError{isfb_config_bad_product_word_count,
                              kErrorOwnershipISFBSize}));

struct TagError {
  tlv_tag_t tag;
  rom_error_t expect;
};

class OwnerBlockPerTagTest : public OwnerBlockTest,
                             public testing::WithParamInterface<TagError> {};

TEST_P(OwnerBlockPerTagTest, ParseBadVersion) {
  EXPECT_CALL(flash_ctrl_, DataDefaultCfgGet)
      .WillRepeatedly(Return(default_config));
  BinaryBlob<owner_block_t> block(basic_owner, sizeof(basic_owner));
  TagError param = GetParam();

  // Rewrite the version to a bad value.
  block.Find(param.tag)
      .Seek(offsetof(tlv_header_t, version))
      .Write((struct_version_t){5, 0});
  owner_config_t config;
  owner_application_keyring_t keyring{};
  rom_error_t error = owner_block_parse(
      block.get(), /*check_only=*/kHardenedBoolFalse, &config, &keyring);
  EXPECT_EQ(error, param.expect);
}

INSTANTIATE_TEST_SUITE_P(
    AllCases, OwnerBlockPerTagTest,
    testing::Values(TagError{kTlvTagOwner, kErrorOwnershipOWNRVersion},
                    TagError{kTlvTagApplicationKey, kErrorOwnershipAPPKVersion},
                    TagError{kTlvTagFlashConfig, kErrorOwnershipFLSHVersion},
                    TagError{kTlvTagInfoConfig, kErrorOwnershipINFOVersion},
                    TagError{kTlvTagRescueConfig, kErrorOwnershipRESQVersion},
                    TagError{kTlvTagIntegrationSpecificFirmwareBinding,
                             kErrorOwnershipISFBVersion}));

// Flash region is the exact size of the ROM_EXT and has a bad ECC setting.
const owner_flash_config_t invalid_flash_0 = {
    .header =
        {
            .tag = kTlvTagFlashConfig,
            .length =
                sizeof(owner_flash_config_t) + 1 * sizeof(owner_flash_region_t),
        },
    .config =
        {
            {
                // SideA ROM_EXT.
                .start = 0,
                .size = 32,
                .access = FLASH_ACCESS(
                    /*index=*/0,
                    /*read=*/true,
                    /*program=*/true,
                    /*erase=*/true,
                    /*pwp=*/true,
                    /*lock=*/false),
                .properties = FLASH_PROP(
                    /*index=*/0,
                    /*scramble=*/false,
                    /*ecc=*/true,
                    /*he=*/false),
            },
        },
};

// Flash region overlaps ROM_EXT and APP.
const owner_flash_config_t invalid_flash_1 = {
    .header =
        {
            .tag = kTlvTagFlashConfig,
            .length =
                sizeof(owner_flash_config_t) + 1 * sizeof(owner_flash_region_t),
        },
    .config =
        {
            {
                // SideA ROM_EXT & APP.
                .start = 0,
                .size = 224,
                .access = FLASH_ACCESS(
                    /*index=*/0,
                    /*read=*/true,
                    /*program=*/true,
                    /*erase=*/true,
                    /*pwp=*/true,
                    /*lock=*/false),
                .properties = FLASH_PROP(
                    /*index=*/0,
                    /*scramble=*/false,
                    /*ecc=*/false,
                    /*he=*/false),
            },
        },
};

// Flash regions straddle ROM_EXT.
const owner_flash_config_t invalid_flash_2 = {
    .header =
        {
            .tag = kTlvTagFlashConfig,
            .length =
                sizeof(owner_flash_config_t) + 2 * sizeof(owner_flash_region_t),
        },
    .config =
        {
            {
                // SideA ROM_EXT.
                .start = 0,
                .size = 16,
                .access = FLASH_ACCESS(
                    /*index=*/0,
                    /*read=*/true,
                    /*program=*/true,
                    /*erase=*/true,
                    /*pwp=*/true,
                    /*lock=*/false),
                .properties = FLASH_PROP(
                    /*index=*/0,
                    /*scramble=*/false,
                    /*ecc=*/false,
                    /*he=*/false),
            },
            {
                // SideA APP
                .start = 16,
                .size = 240,
                .access = FLASH_ACCESS(
                    /*index=*/1,
                    /*read=*/true,
                    /*program=*/true,
                    /*erase=*/true,
                    /*pwp=*/true,
                    /*lock=*/false),
                .properties = FLASH_PROP(
                    /*index=*/1,
                    /*scramble=*/false,
                    /*ecc=*/false,
                    /*he=*/false),
            },
        },
};

// Flash region is the exact size of the ROM_EXT.
const owner_flash_config_t invalid_flash_3 = {
    .header =
        {
            .tag = kTlvTagFlashConfig,
            .length =
                sizeof(owner_flash_config_t) + 2 * sizeof(owner_flash_region_t),
        },
    .config =
        {
            {
                // SideA ROM_EXT.
                .start = 0,
                .size = 32,
                .access = FLASH_ACCESS(
                    /*index=*/0,
                    /*read=*/true,
                    /*program=*/true,
                    /*erase=*/true,
                    /*pwp=*/true,
                    /*lock=*/false),
                .properties = FLASH_PROP(
                    /*index=*/0,
                    /*scramble=*/false,
                    /*ecc=*/false,
                    /*he=*/false),
            },
            {
                // SideB ROM_EXT.
                .start = 256,
                .size = 32,
                .access = FLASH_ACCESS(
                    /*index=*/1,
                    /*read=*/true,
                    /*program=*/true,
                    /*erase=*/true,
                    /*pwp=*/true,
                    /*lock=*/false),
                .properties = FLASH_PROP(
                    /*index=*/1,
                    /*scramble=*/false,
                    /*ecc=*/false,
                    /*he=*/false),
            },
        },

};

// Flash configuration has too many entries.
// We don't have to include the entries because the length is checked first
// and none of the non-existent entries will be accessed.
const owner_flash_config_t invalid_flash_4 = {
    .header =
        {
            .tag = kTlvTagFlashConfig,
            .length =
                sizeof(owner_flash_config_t) + 8 * sizeof(owner_flash_region_t),
        },
};

// Flash configuration extends beyond end of flash
const owner_flash_config_t invalid_flash_5 = {
    .header =
        {
            .tag = kTlvTagFlashConfig,
            .length =
                sizeof(owner_flash_config_t) + 1 * sizeof(owner_flash_region_t),
        },
    .config =
        {
            {
                // SideB APP
                .start = 256 + 32,
                .size = 256,
                .access = FLASH_ACCESS(
                    /*index=*/0,
                    /*read=*/true,
                    /*program=*/true,
                    /*erase=*/true,
                    /*pwp=*/true,
                    /*lock=*/false),
                .properties = FLASH_PROP(
                    /*index=*/0,
                    /*scramble=*/false,
                    /*ecc=*/false,
                    /*he=*/false),
            },
        },
};

// Flash configuration has too many entries for Slot A.
const owner_flash_config_t invalid_flash_6 = {
    .header =
        {
            .tag = kTlvTagFlashConfig,
            .length =
                sizeof(owner_flash_config_t) + 4 * sizeof(owner_flash_region_t),
        },
    .config = {{
                   // SideA APP
                   .start = 32,
                   .size = 1,
                   .access = FLASH_ACCESS(
                       /*index=*/0,
                       /*read=*/true,
                       /*program=*/true,
                       /*erase=*/true,
                       /*pwp=*/true,
                       /*lock=*/false),
                   .properties = FLASH_PROP(
                       /*index=*/0,
                       /*scramble=*/false,
                       /*ecc=*/false,
                       /*he=*/false),
               },
               {
                   // SideA APP
                   .start = 33,
                   .size = 1,
                   .access = FLASH_ACCESS(
                       /*index=*/1,
                       /*read=*/true,
                       /*program=*/true,
                       /*erase=*/true,
                       /*pwp=*/true,
                       /*lock=*/false),
                   .properties = FLASH_PROP(
                       /*index=*/1,
                       /*scramble=*/false,
                       /*ecc=*/false,
                       /*he=*/false),
               },
               {
                   // SideA APP
                   .start = 34,
                   .size = 1,
                   .access = FLASH_ACCESS(
                       /*index=*/2,
                       /*read=*/true,
                       /*program=*/true,
                       /*erase=*/true,
                       /*pwp=*/true,
                       /*lock=*/false),
                   .properties = FLASH_PROP(
                       /*index=*/2,
                       /*scramble=*/false,
                       /*ecc=*/false,
                       /*he=*/false),
               },
               {
                   // SideA APP
                   .start = 35,
                   .size = 1,
                   .access = FLASH_ACCESS(
                       /*index=*/3,
                       /*read=*/true,
                       /*program=*/true,
                       /*erase=*/true,
                       /*pwp=*/true,
                       /*lock=*/false),
                   .properties = FLASH_PROP(
                       /*index=*/3,
                       /*scramble=*/false,
                       /*ecc=*/false,
                       /*he=*/false),
               }},
};

// Flash configuration has too many entries for Slot B.
const owner_flash_config_t invalid_flash_7 = {
    .header =
        {
            .tag = kTlvTagFlashConfig,
            .length =
                sizeof(owner_flash_config_t) + 4 * sizeof(owner_flash_region_t),
        },
    .config = {{
                   // SideB APP
                   .start = 256 + 32,
                   .size = 1,
                   .access = FLASH_ACCESS(
                       /*index=*/0,
                       /*read=*/true,
                       /*program=*/true,
                       /*erase=*/true,
                       /*pwp=*/true,
                       /*lock=*/false),
                   .properties = FLASH_PROP(
                       /*index=*/0,
                       /*scramble=*/false,
                       /*ecc=*/false,
                       /*he=*/false),
               },
               {
                   // SideB APP
                   .start = 256 + 33,
                   .size = 1,
                   .access = FLASH_ACCESS(
                       /*index=*/1,
                       /*read=*/true,
                       /*program=*/true,
                       /*erase=*/true,
                       /*pwp=*/true,
                       /*lock=*/false),
                   .properties = FLASH_PROP(
                       /*index=*/1,
                       /*scramble=*/false,
                       /*ecc=*/false,
                       /*he=*/false),
               },
               {
                   // SideB APP
                   .start = 256 + 34,
                   .size = 1,
                   .access = FLASH_ACCESS(
                       /*index=*/2,
                       /*read=*/true,
                       /*program=*/true,
                       /*erase=*/true,
                       /*pwp=*/true,
                       /*lock=*/false),
                   .properties = FLASH_PROP(
                       /*index=*/2,
                       /*scramble=*/false,
                       /*ecc=*/false,
                       /*he=*/false),
               },
               {
                   // SideB APP
                   .start = 256 + 35,
                   .size = 1,
                   .access = FLASH_ACCESS(
                       /*index=*/3,
                       /*read=*/true,
                       /*program=*/true,
                       /*erase=*/true,
                       /*pwp=*/true,
                       /*lock=*/false),
                   .properties = FLASH_PROP(
                       /*index=*/3,
                       /*scramble=*/false,
                       /*ecc=*/false,
                       /*he=*/false),
               }},
};

class RomExtFlashConfigTest
    : public OwnerBlockTest,
      public testing::WithParamInterface<
          std::tuple<const owner_flash_config_t *, rom_error_t>> {};

// Test bad ROM_EXT region configs with respect to the default config.
TEST_P(RomExtFlashConfigTest, BadFlashConfig) {
  EXPECT_CALL(flash_ctrl_, DataDefaultCfgGet)
      .WillRepeatedly(Return(default_config));
  const owner_flash_config_t *param;
  rom_error_t expected;
  std::tie(param, expected) = GetParam();
  rom_error_t error = owner_block_flash_check(param);
  EXPECT_EQ(error, expected);
}

INSTANTIATE_TEST_SUITE_P(
    AllCases, RomExtFlashConfigTest,
    testing::Values(
        std::make_tuple(&invalid_flash_0, kErrorOwnershipFlashConfigRomExt),
        std::make_tuple(&invalid_flash_1, kErrorOwnershipFlashConfigRomExt),
        std::make_tuple(&invalid_flash_2, kErrorOwnershipFlashConfigRomExt),
        std::make_tuple(&invalid_flash_3, kErrorOwnershipFlashConfigRomExt),
        std::make_tuple(&invalid_flash_4, kErrorOwnershipFlashConfigLength),
        std::make_tuple(&invalid_flash_5, kErrorOwnershipFlashConfigBounds),
        std::make_tuple(&invalid_flash_6, kErrorOwnershipFlashConfigSlots),
        std::make_tuple(&invalid_flash_7, kErrorOwnershipFlashConfigSlots)));

struct FlashRegion {
  uint32_t start;
  uint32_t end;
  bool overlap;
  bool exclusive;
};

class RomExtFlashBoundsTest : public OwnerBlockTest,
                              public testing::WithParamInterface<FlashRegion> {
};

extern "C" {
// These functions aren't defined in owner_block.h because they aren't meant
// to be public APIs.  They aren't static so we can access the symbols here
// for testing.
hardened_bool_t rom_ext_flash_overlap(uint32_t, uint32_t);
hardened_bool_t rom_ext_flash_exclusive(uint32_t, uint32_t);
rom_error_t owner_block_application_key_check(
    const owner_application_key_t *key);
rom_error_t owner_block_flash_info_check(const owner_flash_info_config_t *info);
rom_error_t owner_block_rescue_check(const owner_rescue_config_t *rescue);
}

// Test the flash bounds checking functions.
TEST_P(RomExtFlashBoundsTest, FlashBoundsTest) {
  FlashRegion p = GetParam();
  hardened_bool_t overlap = rom_ext_flash_overlap(p.start, p.end);
  hardened_bool_t exclusive = rom_ext_flash_exclusive(p.start, p.end);
  EXPECT_EQ(overlap, p.overlap ? kHardenedBoolTrue : kHardenedBoolFalse);
  EXPECT_EQ(exclusive, p.exclusive ? kHardenedBoolTrue : kHardenedBoolFalse);
}

// clang-format off
INSTANTIATE_TEST_SUITE_P(AllCases, RomExtFlashBoundsTest,
testing::Values(
  // The ROM_EXT A region is blocks [0x00 .. 0x20).
  // The ROM_EXT B region is blocks [0x100 .. 0x120).
  // The ranges expressed are half-open: [start .. end).
  FlashRegion{0x000, 0x020, /*overlap=*/true, /*exclusive=*/true}, // Full ROM_EXT A region.
  FlashRegion{0x100, 0x120, /*overlap=*/true, /*exclusive=*/true}, // Full ROM_EXT B region.
  FlashRegion{0x005, 0x010, /*overlap=*/true, /*exclusive=*/true}, // Partial ROM_EXT A region.
  FlashRegion{0x105, 0x110, /*overlap=*/true, /*exclusive=*/true}, // Partial ROM_EXT B region.
  FlashRegion{0x000, 0x040, /*overlap=*/true, /*exclusive=*/false}, // Overlapped ROM_EXT A region.
  FlashRegion{0x100, 0x140, /*overlap=*/true, /*exclusive=*/false}, // Overlapped ROM_EXT B region.
  FlashRegion{0x020, 0x040, /*overlap=*/false, /*exclusive=*/false}, // Not ROM_EXT A region.
  FlashRegion{0x120, 0x140, /*overlap=*/false, /*exclusive=*/false}, // Not ROM_EXT B region.
  FlashRegion{0x005, 0x105, /*overlap=*/true, /*exclusive=*/false}, // Mid RX_A to mid RX_B.
  FlashRegion{0x020, 0x100, /*overlap=*/false, /*exclusive=*/false}, // Full not ROM_EXT side A.
  FlashRegion{0x020, 0x101, /*overlap=*/true, /*exclusive=*/false}, // Side A intrudes in to RX_B.
  FlashRegion{0x000, 0x200, /*overlap=*/true, /*exclusive=*/false} // Full flash region.
));
// clang-format on

struct OwnerBlockLengths {
  tlv_tag_t tag;
  int16_t length;
  rom_error_t expect;
};

class OwnerBlockConfigCheckTest
    : public OwnerBlockTest,
      public testing::WithParamInterface<OwnerBlockLengths> {};

// Tests that owner_block_parse checks the lengths of the TLV items in the owner
// config block and returns errors for invalid lengths.
TEST_P(OwnerBlockConfigCheckTest, ConfigBoundsTest) {
  auto param = GetParam();
  BinaryBlob<owner_block_t> block(basic_owner, sizeof(basic_owner));

  if (param.length != -1) {
    block.Find(param.tag)
        .Seek(offsetof(tlv_header_t, length))
        .Write(param.length);
  }

  rom_error_t error = owner_block_parse(
      block.get(), /*check_only=*/kHardenedBoolTrue, nullptr, nullptr);
  EXPECT_EQ(error, param.expect);
}

// clang-format off
INSTANTIATE_TEST_SUITE_P(AllCases, OwnerBlockConfigCheckTest,
testing::Values(
    OwnerBlockLengths{kTlvTagApplicationKey, 40, kErrorOwnershipInvalidTagLength},
    OwnerBlockLengths{kTlvTagApplicationKey, 512, kErrorOwnershipInvalidTagLength},
    OwnerBlockLengths{kTlvTagFlashConfig, 4, kErrorOwnershipInvalidTagLength},
    OwnerBlockLengths{kTlvTagInfoConfig, 4, kErrorOwnershipInvalidTagLength},
    OwnerBlockLengths{kTlvTagRescueConfig, 12, kErrorOwnershipInvalidTagLength}
));
// clang-format on

class ApplicationKeyCheckTest
    : public OwnerBlockTest,
      public testing::WithParamInterface<
          std::tuple<ownership_key_alg_t, rom_error_t>> {};

TEST_P(ApplicationKeyCheckTest, KeyAlgo) {
  ownership_key_alg_t key_alg;
  rom_error_t expect;
  std::tie(key_alg, expect) = GetParam();

  owner_application_key_t key = {
      .header =
          {
              .tag = kTlvTagApplicationKey,
              .length = sizeof(owner_application_key_t),
          },
      .key_alg = key_alg,
  };

  rom_error_t error = owner_block_application_key_check(&key);
  EXPECT_EQ(error, expect);
}

// clang-format off
INSTANTIATE_TEST_SUITE_P(AllCases, ApplicationKeyCheckTest,
testing::Values(
    // Currently supported algorithms:
    std::make_tuple(kOwnershipKeyAlgEcdsaP256, kErrorOk),
    std::make_tuple(kOwnershipKeyAlgHybridSpxPure, kErrorOk),
    std::make_tuple(kOwnershipKeyAlgHybridSpxPrehash, kErrorOk),
    // Currently unsupported algorithms:
    std::make_tuple(kOwnershipKeyAlgSpxPure, kErrorOwnershipInvalidAlgorithm),
    std::make_tuple(kOwnershipKeyAlgSpxPrehash, kErrorOwnershipInvalidAlgorithm),
    std::make_tuple(kOwnershipKeyAlgSq20Pure, kErrorOwnershipInvalidAlgorithm),
    std::make_tuple(kOwnershipKeyAlgSq20Prehash, kErrorOwnershipInvalidAlgorithm),
    std::make_tuple(kOwnershipKeyAlgHybridSq20Pure, kErrorOwnershipInvalidAlgorithm),
    std::make_tuple(kOwnershipKeyAlgHybridSq20Prehash, kErrorOwnershipInvalidAlgorithm)
));
// clang-format on

class RescueCheckTest : public OwnerBlockTest,
                        public testing::WithParamInterface<
                            std::tuple<uint16_t, uint16_t, rom_error_t>> {};

TEST_P(RescueCheckTest, RescueBounds) {
  uint16_t start, size;
  rom_error_t expect;
  std::tie(start, size, expect) = GetParam();

  owner_rescue_config_t rescue = {
      .header =
          {
              .tag = kTlvTagRescueConfig,
              .length = sizeof(owner_rescue_config_t),
          },
      .start = start,
      .size = size,
  };

  rom_error_t error = owner_block_rescue_check(&rescue);
  EXPECT_EQ(error, expect);
}

// clang-format off
INSTANTIATE_TEST_SUITE_P(AllCases, RescueCheckTest,
testing::Values(
    std::make_tuple(32, 224, kErrorOk),
    // Starts in ROM_EXT region.
    std::make_tuple(0, 224, kErrorOwnershipInvalidRescueBounds),
    // Too big
    std::make_tuple(32, 225, kErrorOwnershipInvalidRescueBounds)
));
// clang-format on

class FlashInfoCheckTest : public OwnerBlockTest,
                           public testing::WithParamInterface<
                               std::tuple<uint8_t, uint8_t, rom_error_t>> {};

TEST_P(FlashInfoCheckTest, ValidPage) {
  uint16_t bank, page;
  rom_error_t expect;
  std::tie(bank, page, expect) = GetParam();

  union {
    owner_flash_info_config_t info;
    uint8_t
        memory[sizeof(owner_flash_info_config_t) + sizeof(owner_info_page_t)];
  } data = {.info = {
                .header =
                    {
                        .tag = kTlvTagInfoConfig,
                        .length = sizeof(owner_flash_info_config_t) +
                                  sizeof(owner_info_page_t),
                    },
            }};

  data.info.config[0].bank = bank;
  data.info.config[0].page = page;

  rom_error_t error = owner_block_flash_info_check(&data.info);
  EXPECT_EQ(error, expect);
}

// clang-format off
INSTANTIATE_TEST_SUITE_P(AllCases, FlashInfoCheckTest,
testing::Values(
    // Bank 0 INFO pages:
    std::make_tuple(0, 0, kErrorOwnershipBadInfoPage),
    std::make_tuple(0, 1, kErrorOwnershipBadInfoPage),
    std::make_tuple(0, 2, kErrorOwnershipBadInfoPage),
    std::make_tuple(0, 3, kErrorOwnershipBadInfoPage),
    std::make_tuple(0, 4, kErrorOwnershipBadInfoPage),
    std::make_tuple(0, 5, kErrorOk),
    std::make_tuple(0, 6, kErrorOk),
    std::make_tuple(0, 7, kErrorOk),
    std::make_tuple(0, 8, kErrorOk),
    std::make_tuple(0, 9, kErrorOwnershipBadInfoPage),

    // Bank 1 INFO pages:
    std::make_tuple(1, 0, kErrorOwnershipBadInfoPage),
    std::make_tuple(1, 1, kErrorOwnershipBadInfoPage),
    std::make_tuple(1, 2, kErrorOwnershipBadInfoPage),
    std::make_tuple(1, 3, kErrorOwnershipBadInfoPage),
    std::make_tuple(1, 4, kErrorOwnershipBadInfoPage),
    std::make_tuple(1, 5, kErrorOk),
    std::make_tuple(1, 6, kErrorOk),
    std::make_tuple(1, 7, kErrorOk),
    std::make_tuple(1, 8, kErrorOk),
    std::make_tuple(1, 9, kErrorOwnershipBadInfoPage)
));
// clang-format on

}  // namespace
