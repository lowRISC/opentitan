// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/ownership/owner_block.h"

#include <stdint.h>

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
using ::testutil::BinaryBlob;

class OwnerBlockTest : public rom_test::RomTest {
 protected:
  MockFlashCtrl flash_ctrl_;
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
                sizeof(owner_flash_config_t) + 6 * sizeof(owner_flash_region_t),
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
                .size = 32,
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
                .size = 32,
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
        },
};

const owner_flash_config_t bad_flash_config = {
    .header =
        {
            .tag = kTlvTagFlashConfig,
            .length =
                sizeof(owner_flash_config_t) + 8 * sizeof(owner_flash_region_t),
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
                .page = 5,
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

TEST_F(OwnerBlockTest, FlashConfigApplyBad) {
  rom_error_t error = owner_block_flash_apply(&bad_flash_config, kBootSlotA, 0);
  EXPECT_EQ(error, kErrorOwnershipFlashConfigLenth);
}

// Tests that the flash parameters get applied for side A.
TEST_F(OwnerBlockTest, FlashConfigApplySideA) {
  EXPECT_CALL(
      flash_ctrl_,
      DataRegionProtect(0, 0, 32,
                        FlashPerms(kMultiBitBool4True, kMultiBitBool4True,
                                   kMultiBitBool4True),
                        FlashCfg(kMultiBitBool4False, kMultiBitBool4False,
                                 kMultiBitBool4False),
                        kHardenedBoolFalse));
  EXPECT_CALL(
      flash_ctrl_,
      DataRegionProtect(
          1, 32, 192,
          FlashPerms(kMultiBitBool4True, kMultiBitBool4True,
                     kMultiBitBool4True),
          FlashCfg(kMultiBitBool4True, kMultiBitBool4True, kMultiBitBool4False),
          kHardenedBoolFalse));
  EXPECT_CALL(
      flash_ctrl_,
      DataRegionProtect(2, 224, 32,
                        FlashPerms(kMultiBitBool4True, kMultiBitBool4True,
                                   kMultiBitBool4True),
                        FlashCfg(kMultiBitBool4False, kMultiBitBool4False,
                                 kMultiBitBool4True),
                        kHardenedBoolFalse));

  rom_error_t error =
      owner_block_flash_apply(&simple_flash_config, kBootSlotA, 0);
  EXPECT_EQ(error, kErrorOk);
}

// Tests that the flash parameters get applied for side A and the
// ProtectWhenPrimary disables erase and program on the ROM_EXT and FIRMWARE
// regions.
TEST_F(OwnerBlockTest, FlashConfigApplySideAPrimary) {
  EXPECT_CALL(
      flash_ctrl_,
      DataRegionProtect(0, 0, 32,
                        FlashPerms(kMultiBitBool4True, kMultiBitBool4False,
                                   kMultiBitBool4False),
                        FlashCfg(kMultiBitBool4False, kMultiBitBool4False,
                                 kMultiBitBool4False),
                        kHardenedBoolFalse));
  EXPECT_CALL(
      flash_ctrl_,
      DataRegionProtect(
          1, 32, 192,
          FlashPerms(kMultiBitBool4True, kMultiBitBool4False,
                     kMultiBitBool4False),
          FlashCfg(kMultiBitBool4True, kMultiBitBool4True, kMultiBitBool4False),
          kHardenedBoolFalse));
  EXPECT_CALL(
      flash_ctrl_,
      DataRegionProtect(2, 224, 32,
                        FlashPerms(kMultiBitBool4True, kMultiBitBool4True,
                                   kMultiBitBool4True),
                        FlashCfg(kMultiBitBool4False, kMultiBitBool4False,
                                 kMultiBitBool4True),
                        kHardenedBoolFalse));

  rom_error_t error =
      owner_block_flash_apply(&simple_flash_config, kBootSlotA, kBootSlotA);
  EXPECT_EQ(error, kErrorOk);
}

// Tests that the flash parameters get applied for side B.
TEST_F(OwnerBlockTest, FlashConfigApplySideB) {
  EXPECT_CALL(
      flash_ctrl_,
      DataRegionProtect(3, 256 + 0, 32,
                        FlashPerms(kMultiBitBool4True, kMultiBitBool4True,
                                   kMultiBitBool4True),
                        FlashCfg(kMultiBitBool4False, kMultiBitBool4False,
                                 kMultiBitBool4False),
                        kHardenedBoolFalse));
  EXPECT_CALL(
      flash_ctrl_,
      DataRegionProtect(
          4, 256 + 32, 192,
          FlashPerms(kMultiBitBool4True, kMultiBitBool4True,
                     kMultiBitBool4True),
          FlashCfg(kMultiBitBool4True, kMultiBitBool4True, kMultiBitBool4False),
          kHardenedBoolFalse));
  EXPECT_CALL(
      flash_ctrl_,
      DataRegionProtect(5, 256 + 224, 32,
                        FlashPerms(kMultiBitBool4True, kMultiBitBool4True,
                                   kMultiBitBool4True),
                        FlashCfg(kMultiBitBool4False, kMultiBitBool4False,
                                 kMultiBitBool4True),
                        kHardenedBoolFalse));

  rom_error_t error =
      owner_block_flash_apply(&simple_flash_config, kBootSlotB, 0);
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

  rom_error_t error = owner_block_parse(block.get(), &config, &keyring);
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
  rom_error_t error = owner_block_parse(block.get(), &config, &keyring);
  EXPECT_EQ(error, kErrorOwnershipInvalidTagLength);
}

TEST_F(OwnerBlockTest, ParseBlockBadHeaderTag) {
  BinaryBlob<owner_block_t> block(basic_owner, sizeof(basic_owner));
  // Rewrite the header tag from `OWNR` to `AAAA`.
  block.Seek(offsetof(owner_block_t, header.tag)).Write(0x41414141);
  owner_config_t config;
  owner_application_keyring_t keyring{};
  rom_error_t error = owner_block_parse(block.get(), &config, &keyring);
  EXPECT_EQ(error, kErrorOwnershipInvalidTag);
}

TEST_F(OwnerBlockTest, ParseBlockBadStructVersion) {
  BinaryBlob<owner_block_t> block(basic_owner, sizeof(basic_owner));
  // Rewrite the struct_version to a bad value.
  block.Seek(offsetof(owner_block_t, struct_version)).Write(2);
  owner_config_t config;
  owner_application_keyring_t keyring{};
  rom_error_t error = owner_block_parse(block.get(), &config, &keyring);
  EXPECT_EQ(error, kErrorOwnershipInvalidVersion);
}

TEST_F(OwnerBlockTest, ParseBlockUnknownTag) {
  BinaryBlob<owner_block_t> block(basic_owner, sizeof(basic_owner));
  // Write an unknown header of {tag="AAAA", len=0x40} after the RESQ config.
  uint32_t len =
      block.Find(kTlvTagRescueConfig).Seek(sizeof(uint32_t)).Read<uint32_t>() -
      sizeof(tlv_header_t);
  block.Seek(len).Write(0x41414141).Write(0x40);
  owner_config_t config;
  owner_application_keyring_t keyring{};
  rom_error_t error = owner_block_parse(block.get(), &config, &keyring);
  EXPECT_EQ(error, kErrorOwnershipInvalidTag);
}

TEST_F(OwnerBlockTest, ParseBlockBadLength) {
  BinaryBlob<owner_block_t> block(basic_owner, sizeof(basic_owner));
  // Rewrite the RESQ block length to overflow the TLV region.
  block.Find(kTlvTagRescueConfig).Seek(sizeof(uint32_t)).Write(uint32_t(0x5f1));
  owner_config_t config;
  owner_application_keyring_t keyring{};
  rom_error_t error = owner_block_parse(block.get(), &config, &keyring);
  EXPECT_EQ(error, kErrorOwnershipInvalidTagLength);
}

TEST_F(OwnerBlockTest, ParseBlockDupFlash) {
  BinaryBlob<owner_block_t> block(basic_owner, sizeof(basic_owner));
  // Rewrite the RESQ tag as a FLSH tag to test duplicate detection.
  block.Find(kTlvTagRescueConfig).Write(kTlvTagFlashConfig);
  owner_config_t config;
  owner_application_keyring_t keyring{};
  rom_error_t error = owner_block_parse(block.get(), &config, &keyring);
  EXPECT_EQ(error, kErrorOwnershipDuplicateItem);
}

TEST_F(OwnerBlockTest, ParseBlockDupInfo) {
  BinaryBlob<owner_block_t> block(basic_owner, sizeof(basic_owner));
  // Rewrite the RESQ tag as an INFO tag to test duplicate detection.
  block.Find(kTlvTagRescueConfig).Write(kTlvTagInfoConfig);
  owner_config_t config;
  owner_application_keyring_t keyring{};
  rom_error_t error = owner_block_parse(block.get(), &config, &keyring);
  EXPECT_EQ(error, kErrorOwnershipDuplicateItem);
}

TEST_F(OwnerBlockTest, ParseBlockDupRescue) {
  BinaryBlob<owner_block_t> block(basic_owner, sizeof(basic_owner));
  // Rewrite the FLSH tag as a RESQ tag to test duplicate detection.
  block.Find(kTlvTagFlashConfig).Write(kTlvTagRescueConfig);
  owner_config_t config;
  owner_application_keyring_t keyring{};
  rom_error_t error = owner_block_parse(block.get(), &config, &keyring);
  EXPECT_EQ(error, kErrorOwnershipDuplicateItem);
}
}  // namespace
