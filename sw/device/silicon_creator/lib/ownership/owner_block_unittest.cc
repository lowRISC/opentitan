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

TEST_F(OwnerBlockTest, FlashInfoApply) {
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
                    TagError{kTlvTagRescueConfig, kErrorOwnershipRESQVersion}));

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

}  // namespace
