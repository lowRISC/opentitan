// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/boot_log.h"

#include <cstring>

#include "gtest/gtest.h"
#include "sw/device/silicon_creator/lib/chip_info.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/mock_hmac.h"

bool operator==(hmac_digest_t lhs, hmac_digest_t rhs) {
  return std::memcmp(&lhs, &rhs, sizeof(hmac_digest_t)) == 0;
}

bool operator!=(hmac_digest_t lhs, hmac_digest_t rhs) {
  return std::memcmp(&lhs, &rhs, sizeof(hmac_digest_t)) != 0;
}

bool operator==(chip_info_scm_revision_t lhs, chip_info_scm_revision_t rhs) {
  return std::memcmp(&lhs, &rhs, sizeof(chip_info_scm_revision_t)) == 0;
}

namespace boot_log_unittest {
namespace {

using ::testing::_;

class BootLogTest : public rom_test::RomTest {
 protected:
  rom_test::MockHmac hmac_sha256_;

  hmac_digest_t expected_digest = {
      .digest =
          {
              0x11111111,
              0x22222222,
              0x33333333,
              0x44444444,
              0xaaaaaaaa,
              0xbbbbbbbb,
              0xcccccccc,
              0xdddddddd,
          },
  };

  chip_info_scm_revision_t expected_chip_version = {
      .scm_revision_low = 0x76543210,
      .scm_revision_high = 0xcafecafe,
  };

  uint32_t expected_rom_ext_slot = kRomExtBootSlotA;
  uint32_t expected_bl0_slot = kBl0BootSlotB;

  boot_log_t boot_log = {
      .digest = expected_digest,
      .identifier = kBootLogIdentifier,
      .chip_version = expected_chip_version,
      .rom_ext_slot = expected_rom_ext_slot,
      .bl0_slot = expected_bl0_slot,
  };
};

TEST_F(BootLogTest, DigestUpdate) {
  // Have the HMAC function return a different digest
  hmac_digest_t new_digest = {
      .digest =
          {
              0xffffffff,
              0xeeeeeeee,
              0xdddddddd,
              0xcccccccc,
              0x00000000,
              0x11111111,
              0x22222222,
              0x33333333,
          },
  };
  EXPECT_NE(new_digest, expected_digest);

  void *expected_digest_region_start =
      (char *)&boot_log + sizeof(hmac_digest_t);
  size_t expected_digest_region_len =
      sizeof(boot_log_t) - sizeof(hmac_digest_t);
  EXPECT_CALL(hmac_sha256_, sha256(expected_digest_region_start,
                                   expected_digest_region_len, _))
      .WillOnce(testing::SetArgPointee<2>(new_digest));

  boot_log_digest_update(&boot_log);

  // Check that the digest field in boot_log has been updated correctly
  EXPECT_EQ(new_digest, boot_log.digest);
  // Ensure no other fields changed
  EXPECT_EQ(kBootLogIdentifier, boot_log.identifier);
  EXPECT_EQ(expected_rom_ext_slot, boot_log.rom_ext_slot);
  EXPECT_EQ(expected_bl0_slot, boot_log.bl0_slot);
  EXPECT_EQ(expected_chip_version, boot_log.chip_version);
}

TEST_F(BootLogTest, BootLogCheckSuccess) {
  // Have the HMAC function return a matching digest
  hmac_digest_t new_digest = {
      .digest =
          {
              0x11111111,
              0x22222222,
              0x33333333,
              0x44444444,
              0xaaaaaaaa,
              0xbbbbbbbb,
              0xcccccccc,
              0xdddddddd,
          },
  };
  EXPECT_EQ(new_digest, expected_digest);

  void *expected_digest_region_start =
      (char *)&boot_log + sizeof(hmac_digest_t);
  size_t expected_digest_region_len =
      sizeof(boot_log_t) - sizeof(hmac_digest_t);
  EXPECT_CALL(hmac_sha256_, sha256(expected_digest_region_start,
                                   expected_digest_region_len, _))
      .WillOnce(testing::SetArgPointee<2>(new_digest));

  uint32_t error = boot_log_check(&boot_log);
  EXPECT_EQ(error, kErrorOk);

  // Ensure no fields have been changed
  EXPECT_EQ(expected_digest, boot_log.digest);
  EXPECT_EQ(kBootLogIdentifier, boot_log.identifier);
  EXPECT_EQ(expected_rom_ext_slot, boot_log.rom_ext_slot);
  EXPECT_EQ(expected_bl0_slot, boot_log.bl0_slot);
  EXPECT_EQ(expected_chip_version, boot_log.chip_version);
}

TEST_F(BootLogTest, BootLogCheckFailure) {
  // Have the HMAC function return a non-matching digest
  hmac_digest_t new_digest = {
      .digest =
          {
              0x21111111,
              0x22222222,
              0x33333333,
              0x44444444,
              0xaaaaaaaa,
              0xbbbbbbbb,
              0xcccccccc,
              0xdddddddd,
          },
  };
  EXPECT_NE(new_digest, expected_digest);

  void *expected_digest_region_start =
      (char *)&boot_log + sizeof(hmac_digest_t);
  size_t expected_digest_region_len =
      sizeof(boot_log_t) - sizeof(hmac_digest_t);
  EXPECT_CALL(hmac_sha256_, sha256(expected_digest_region_start,
                                   expected_digest_region_len, _))
      .WillOnce(testing::SetArgPointee<2>(new_digest));

  uint32_t error = boot_log_check(&boot_log);
  EXPECT_EQ(error, kErrorBootLogInvalid);

  // Ensure no fields have been changed
  EXPECT_EQ(expected_digest, boot_log.digest);
  EXPECT_EQ(kBootLogIdentifier, boot_log.identifier);
  EXPECT_EQ(expected_rom_ext_slot, boot_log.rom_ext_slot);
  EXPECT_EQ(expected_bl0_slot, boot_log.bl0_slot);
  EXPECT_EQ(expected_chip_version, boot_log.chip_version);
}

}  // namespace
}  // namespace boot_log_unittest
