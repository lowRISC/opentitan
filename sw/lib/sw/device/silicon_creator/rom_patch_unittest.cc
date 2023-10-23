// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/lib/sw/device/silicon_creator/rom_patch.h"

#include <array>
#include <cstring>

#include "gtest/gtest.h"
#include "sw/device/silicon_creator/lib/drivers/mock_hmac.h"
#include "sw/device/silicon_creator/lib/drivers/mock_otp.h"
#include "sw/lib/sw/device/base/mmio.h"
#include "sw/lib/sw/device/silicon_creator/base/mock_sec_mmio.h"
#include "sw/lib/sw/device/silicon_creator/error.h"
#include "sw/lib/sw/device/silicon_creator/testing/rom_test.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"
#include "otp_ctrl_regs.h"  // Generated.

namespace rom_patch_unittest {
namespace {
using ::testing::_;
using ::testing::DoAll;
using ::testing::ElementsAre;
using ::testing::ElementsAreArray;
using ::testing::Return;
using ::testing::SetArgPointee;

class RomPatchTest : public rom_test::RomTest {
 protected:
  rom_test::MockSecMmio mmio_;
  rom_test::MockHmac hmac_;
  rom_test::MockOtp otp_;

  const uint32_t otp_base_ = OTP_CTRL_PARAM_ROM_PATCH_OFFSET;
  const uint32_t env_size_words_ =
      (sizeof((struct rom_patch){0}.table) +
       sizeof((struct rom_patch){0}.header) + kSigVerifyRsaNumBytes) >>
      2;
  const uint32_t preamble_size_words_ =
      (sizeof((struct rom_patch){0}.table) +
       sizeof((struct rom_patch){0}.header)) >>
      2;

  uint32_t RomPatchHeader(uint16_t size, uint8_t lock, uint8_t revision) {
    return lock | (size << 8) | (revision << 24);
  }

  rom_patch_info_t RomPatchInfo(uintptr_t addr, uint16_t size, uint8_t lock,
                                uint8_t revision) {
    rom_patch_info_t info{.addr = addr,
                          .header = RomPatchHeader(size, lock, revision)};
    return info;
  }

  uint32_t RomPatchMatchMBase(uintptr_t addr, uint16_t size, bool locked) {
    return (locked << 31) | ((size & 0xf) << 27) | addr;
  }

  /*
   * For testing purposes, we're initializing the code array so that each
   * element is the address where it will be remapped, or 0 if it's not
   * remapped.
   */
  void RomPatchInitCode(rom_patch_t *patch, uint32_t *code,
                        size_t code_size_words) {
    memset(code, 0, code_size_words * sizeof(uint32_t));
    uint32_t remap_addr = patch->table[0].r_base;
    for (uint32_t slot = 0; slot < RV_CORE_IBEX_PARAM_NUM_REGIONS; slot++) {
      const rom_patch_match_regs_t *match = &patch->table[slot];
      if (!match->m_base || !match->r_base) {
        continue;
      }

      uint8_t region_size_words = (match->m_base >> 27) & 0xf;
      uint32_t region_offset_words = (match->r_base - remap_addr) >> 2;
      for (uint8_t idx = 0; idx < region_size_words; idx++) {
        EXPECT_GT(code_size_words, region_offset_words + idx);
        code[region_offset_words + idx] = match->r_base + (idx << 2);
      }
    }
  }

  uintptr_t ExpectRomPatchLatestTwoPatches(uint8_t first_patch_version,
                                           uint8_t second_patch_version,
                                           uint16_t patch_size) {
    uint32_t first_patch_addr = otp_base_;
    uint32_t second_patch_addr = otp_base_ + (patch_size << 2);
    uint32_t first_patch_header =
        RomPatchHeader(patch_size, kMultiBitBool4True, first_patch_version);
    uint32_t second_patch_header =
        RomPatchHeader(patch_size, kMultiBitBool4True, second_patch_version);

    EXPECT_CALL(otp_, read32(first_patch_addr))
        .WillOnce(Return(first_patch_header));

    EXPECT_CALL(otp_, read32(second_patch_addr))
        .WillOnce(Return(second_patch_header));

    EXPECT_CALL(otp_, read32(second_patch_addr + (patch_size << 2)))
        .WillOnce(Return(0));

    return first_patch_addr;
  }

  void ExpectRomPatchApply(rom_patch_t *patch, hmac_digest_t *digest,
                           uint32_t code[], size_t code_size_words) {
    const uint32_t ibex_base_ = TOP_DARJEELING_RV_CORE_IBEX_CFG_BASE_ADDR;

    EXPECT_CALL(hmac_, sha256_init);

    /* Patch preamble OTP read */
    const uint32_t *otp_data = (uint32_t *)patch;
    EXPECT_CALL(otp_, read(otp_base_, _, _))
        .WillOnce([otp_data, this](auto, uint32_t *data, size_t num_words) {
          EXPECT_EQ(num_words, preamble_size_words_);
          for (uint8_t idx = 0; idx < preamble_size_words_; ++idx) {
            data[idx] = otp_data[idx];
          }
        });

    /* HMAC SHA256 update */
    uint8_t *data = (uint8_t *)patch;
    EXPECT_CALL(hmac_, sha256_update(_, (preamble_size_words_ << 2) - 1))
        .WillOnce(DoAll([data, this](const void *digest_region, size_t size) {
          int digest_region_cmp = std::memcmp(
              digest_region, reinterpret_cast<const char *>(data) + 1,
              (preamble_size_words_ << 2) - 1);
          EXPECT_EQ(digest_region_cmp, 0);
          return kErrorOk;
        }));

    /* Patch code OTP read */
    uint32_t remap_addr = patch->table[0].r_base;
    for (uint8_t idx = 0; idx < code_size_words << 2; idx += 4) {
      EXPECT_CALL(otp_, read32(otp_base_ + (preamble_size_words_ << 2) + idx))
          .WillOnce(Return(code[idx >> 2]));
      EXPECT_CALL(hmac_, sha256_update(_, sizeof(uint32_t)));
      EXPECT_SEC_WRITE32(remap_addr + idx, code[idx >> 2]);
    }

    /* HMAC SHA256 finalization */
    EXPECT_CALL(hmac_, sha256_final(_))
        .WillOnce(DoAll(SetArgPointee<0>(*digest), Return(kErrorOk)));

    /* Ibex remapping */
    for (uint32_t slot = 0; slot < RV_CORE_IBEX_PARAM_NUM_REGIONS; slot++) {
      const rom_patch_match_regs_t *match = &patch->table[slot];
      uint32_t offset = slot * 4;
      if (!match->m_base || !match->r_base) {
        continue;
      }

      uint8_t region_size_words = (match->m_base >> 27) & 0xf;
      uint32_t mask =
          (match->m_base & 0x7ffffff) | (((region_size_words << 2) - 1) >> 1);
      EXPECT_SEC_WRITE32(
          ibex_base_ + RV_CORE_IBEX_IBUS_ADDR_MATCHING_0_REG_OFFSET + offset,
          mask);
      EXPECT_SEC_WRITE32(
          ibex_base_ + RV_CORE_IBEX_DBUS_ADDR_MATCHING_0_REG_OFFSET + offset,
          mask);

      EXPECT_SEC_WRITE32(
          ibex_base_ + RV_CORE_IBEX_IBUS_REMAP_ADDR_0_REG_OFFSET + offset,
          match->r_base);
      EXPECT_SEC_WRITE32(
          ibex_base_ + RV_CORE_IBEX_DBUS_REMAP_ADDR_0_REG_OFFSET + offset,
          match->r_base);

      /* Check that we're remapping the right code */
      uint32_t region_offset_words = (match->r_base - remap_addr) >> 2;
      for (uint8_t idx = 0; idx < region_size_words; idx++) {
        EXPECT_EQ(match->r_base + (idx << 2), code[region_offset_words + idx]);
      }

      EXPECT_SEC_WRITE32(
          ibex_base_ + RV_CORE_IBEX_IBUS_ADDR_EN_0_REG_OFFSET + offset, 1);
      EXPECT_SEC_WRITE32(
          ibex_base_ + RV_CORE_IBEX_DBUS_ADDR_EN_0_REG_OFFSET + offset, 1);

      if (match->m_base >> 31) {
        EXPECT_SEC_WRITE32(
            ibex_base_ + RV_CORE_IBEX_IBUS_REGWEN_0_REG_OFFSET + offset, 1);
        EXPECT_SEC_WRITE32(
            ibex_base_ + RV_CORE_IBEX_DBUS_REGWEN_0_REG_OFFSET + offset, 1);
      }
    }
  }
};

TEST_F(RomPatchTest, PatchValidInvalidAddr) {
  rom_patch_info_t info = RomPatchInfo(kRomPatchInvalidAddr, 0, 0, 0);
  EXPECT_EQ(rom_patch_valid(&info), false);
}

TEST_F(RomPatchTest, PatchValidMaxAddr) {
  rom_patch_info_t info =
      RomPatchInfo(otp_base_ + OTP_CTRL_PARAM_ROM_PATCH_SIZE, 0, 0, 0);
  EXPECT_EQ(rom_patch_valid(&info), false);
}

TEST_F(RomPatchTest, PatchValidMinAddr) {
  rom_patch_info_t info = RomPatchInfo(otp_base_ - 1, 0, 0, 0);
  EXPECT_EQ(rom_patch_valid(&info), false);
}

TEST_F(RomPatchTest, PatchInvalidSize) {
  rom_patch_info_t info = RomPatchInfo(otp_base_, env_size_words_, 0, 0);
  EXPECT_EQ(rom_patch_valid(&info), false);
}

TEST_F(RomPatchTest, PatchValidSize) {
  rom_patch_info_t info = RomPatchInfo(otp_base_, env_size_words_ + 1, 0, 0);
  EXPECT_EQ(rom_patch_valid(&info), true);
}

TEST_F(RomPatchTest, PatchLatestInvalidPatchFromStart) {
  uint16_t patch_size = env_size_words_;
  EXPECT_CALL(otp_, read32(otp_base_))
      .WillOnce(Return(RomPatchHeader(patch_size, kMultiBitBool4True, 1)));

  EXPECT_CALL(otp_, read32(otp_base_ + (patch_size << 2))).WillOnce(Return(0));

  rom_patch_info_t latest = rom_patch_latest(NULL);
  EXPECT_EQ(rom_patch_valid(&latest), false);
}

TEST_F(RomPatchTest, PatchLatestValidSinglePatchFromBase) {
  uint16_t patch_size = env_size_words_ + 1;
  EXPECT_CALL(otp_, read32(otp_base_))
      .WillOnce(Return(RomPatchHeader(patch_size, kMultiBitBool4True, 1)));

  EXPECT_CALL(otp_, read32(otp_base_ + (patch_size << 2))).WillOnce(Return(0));

  EXPECT_EQ(rom_patch_latest(NULL).addr, otp_base_);
}

TEST_F(RomPatchTest, PatchLatestValidTwoPatchesFromBase) {
  uint16_t patch_size = env_size_words_ + 1;
  uintptr_t addr = ExpectRomPatchLatestTwoPatches(1, 2, patch_size);
  EXPECT_EQ(rom_patch_latest(NULL).addr, addr + (patch_size << 2));
}

TEST_F(RomPatchTest, PatchLatestValidPatchFromMax) {
  uint16_t patch_size = env_size_words_ + 1;
  uint8_t second_patch_version = 2;
  uintptr_t addr = ExpectRomPatchLatestTwoPatches(
      second_patch_version - 1, second_patch_version, patch_size);
  rom_patch_info_t second_patch =
      RomPatchInfo(addr + (patch_size << 2), patch_size, kMultiBitBool4True,
                   second_patch_version);
  EXPECT_EQ(rom_patch_latest(&second_patch).addr, addr);
}

TEST_F(RomPatchTest, PatchLatestHigherPatchFromMax) {
  uint16_t patch_size = env_size_words_ + 1;
  uint8_t second_patch_version = 2;
  uintptr_t addr = ExpectRomPatchLatestTwoPatches(
      second_patch_version + 1, second_patch_version, patch_size);

  rom_patch_info_t second_patch =
      RomPatchInfo(addr + (patch_size << 2), patch_size, kMultiBitBool4True,
                   second_patch_version);
  EXPECT_EQ(rom_patch_latest(&second_patch).addr, kRomPatchInvalidAddr);
}

TEST_F(RomPatchTest, PatchLatestEqualPatchFromMax) {
  uint16_t patch_size = env_size_words_ + 1;
  uint8_t second_patch_version = 2;
  uintptr_t addr = ExpectRomPatchLatestTwoPatches(
      second_patch_version, second_patch_version, patch_size);

  rom_patch_info_t second_patch =
      RomPatchInfo(addr + (patch_size << 2), patch_size, kMultiBitBool4True,
                   second_patch_version);
  EXPECT_EQ(rom_patch_latest(&second_patch).addr, addr);
}

TEST_F(RomPatchTest, PatchApplySingleRegion) {
  uint32_t match_addr = 0x20000;
  uint32_t remap_addr = 0x10004000;
  uint16_t patch_code_size = 1;
  uint32_t patch_code[patch_code_size];
  uint16_t patch_size = env_size_words_ + patch_code_size;
  hmac_digest_t digest;
  rom_patch_info_t info =
      RomPatchInfo(otp_base_, patch_size, kMultiBitBool4True, 1);
  rom_patch_t patch = {
      .header = RomPatchHeader(patch_size, kMultiBitBool4True, 1),
      .table =
          {
              [0] =
                  {
                      .m_base =
                          RomPatchMatchMBase(match_addr, patch_code_size, true),
                      .r_base = remap_addr,
                  },
          },
  };

  RomPatchInitCode(&patch, patch_code, patch_code_size);
  ExpectRomPatchApply(&patch, &digest, patch_code, patch_code_size);
  EXPECT_EQ(rom_patch_apply(&info, &digest), kErrorOk);
}

TEST_F(RomPatchTest, PatchApplyTwoRegions) {
  uint32_t match_addr_r1 = 0x20000;
  uint32_t match_addr_r2 = 0x20200;
  uint32_t remap_addr = 0x10004000;
  uint16_t patch_code_size = 5;
  uint32_t patch_code[patch_code_size];
  uint16_t patch_size = env_size_words_ + patch_code_size;
  hmac_digest_t digest;
  rom_patch_info_t info =
      RomPatchInfo(otp_base_, patch_size, kMultiBitBool4True, 1);
  rom_patch_t patch = {
      .header = RomPatchHeader(patch_size, kMultiBitBool4True, 1),
      .table =
          {
              [0] =
                  {
                      .m_base = RomPatchMatchMBase(match_addr_r1, 1, true),
                      .r_base = remap_addr,
                  },
              [1] =
                  {
                      .m_base = RomPatchMatchMBase(match_addr_r2, 2, true),
                      .r_base = remap_addr + 0x8,
                  },
          },
  };

  RomPatchInitCode(&patch, patch_code, patch_code_size);
  ExpectRomPatchApply(&patch, &digest, patch_code, patch_code_size);
  EXPECT_EQ(rom_patch_apply(&info, &digest), kErrorOk);
}

}  // namespace
}  // namespace rom_patch_unittest
