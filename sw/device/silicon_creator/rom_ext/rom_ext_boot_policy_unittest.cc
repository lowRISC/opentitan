// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom_ext/rom_ext_boot_policy.h"

#include "gtest/gtest.h"
#include "sw/device/silicon_creator/lib/mock_boot_data.h"
#include "sw/device/silicon_creator/lib/mock_manifest.h"
#include "sw/device/silicon_creator/rom_ext/mock_rom_ext_boot_policy_ptrs.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace manifest_unittest {
namespace {
using ::testing::Return;

class RomExtBootPolicyTest : public rom_test::RomTest {
 protected:
  rom_test::MockRomExtBootPolicyPtrs rom_ext_boot_policy_ptrs_;
  rom_test::MockManifest mock_manifest_;
  rom_test::MockBootData mock_boot_data_;
};

// TODO(#21204): Refactor to use `manifest_check` from `lib/manifest.h`.
TEST_F(RomExtBootPolicyTest, DISABLED_ManifestCheck) {
  boot_data_t boot_data{{0}};

  manifest_t manifest{};
  manifest.identifier = CHIP_BL0_IDENTIFIER;

  manifest.length = CHIP_BL0_SIZE_MIN;
  EXPECT_CALL(mock_manifest_, Check(&manifest)).WillOnce(Return(kErrorOk));
  EXPECT_EQ(rom_ext_boot_policy_manifest_check(&manifest, &boot_data),
            kErrorOk);

  manifest.length = CHIP_BL0_SIZE_MAX >> 1;
  EXPECT_CALL(mock_manifest_, Check(&manifest)).WillOnce(Return(kErrorOk));
  EXPECT_EQ(rom_ext_boot_policy_manifest_check(&manifest, &boot_data),
            kErrorOk);

  manifest.length = CHIP_BL0_SIZE_MAX;
  EXPECT_CALL(mock_manifest_, Check(&manifest)).WillOnce(Return(kErrorOk));
  EXPECT_EQ(rom_ext_boot_policy_manifest_check(&manifest, &boot_data),
            kErrorOk);
}

TEST_F(RomExtBootPolicyTest, ManifestCheckBadIdentifier) {
  boot_data_t boot_data{};
  manifest_t manifest{};

  EXPECT_EQ(rom_ext_boot_policy_manifest_check(&manifest, &boot_data),
            kErrorBootPolicyBadIdentifier);
}

TEST_F(RomExtBootPolicyTest, ManifestCheckBadLength) {
  boot_data_t boot_data{};
  manifest_t manifest{};
  manifest.identifier = CHIP_BL0_IDENTIFIER;

  manifest.length = CHIP_BL0_SIZE_MIN - 1;
  EXPECT_EQ(rom_ext_boot_policy_manifest_check(&manifest, &boot_data),
            kErrorBootPolicyBadLength);

  manifest.length = CHIP_BL0_SIZE_MAX + 1;
  EXPECT_EQ(rom_ext_boot_policy_manifest_check(&manifest, &boot_data),
            kErrorBootPolicyBadLength);
}

TEST_F(RomExtBootPolicyTest, ManifestCheckBadBl0SecVer) {
  boot_data_t boot_data{};
  boot_data.min_security_version_bl0 = 1;

  manifest_t manifest{};
  manifest.identifier = CHIP_BL0_IDENTIFIER;
  manifest.length = CHIP_BL0_SIZE_MIN;
  manifest.security_version = 0;

  EXPECT_EQ(rom_ext_boot_policy_manifest_check(&manifest, &boot_data),
            kErrorBootPolicyRollback);
}

struct ManifestOrderTestCase {
  uint32_t primary;
};

class ManifestOrderTest
    : public RomExtBootPolicyTest,
      public testing::WithParamInterface<ManifestOrderTestCase> {};

TEST_P(ManifestOrderTest, ManifestsGet) {
  manifest_t manifest_a{};
  manifest_t manifest_b{};
  manifest_a.security_version = 0;
  manifest_b.security_version = 1;

  EXPECT_CALL(rom_ext_boot_policy_ptrs_, ManifestA)
      .WillOnce(Return(&manifest_a));
  EXPECT_CALL(rom_ext_boot_policy_ptrs_, ManifestB)
      .WillOnce(Return(&manifest_b));

  boot_data_t boot_data{};
  if (GetParam().primary == kBootSlotA) {
    boot_data.primary_bl0_slot = kBootSlotA;
  } else {
    boot_data.primary_bl0_slot = kBootSlotB;
  }

  rom_ext_boot_policy_manifests_t res =
      rom_ext_boot_policy_manifests_get(&boot_data);
  if (GetParam().primary == kBootSlotA) {
    EXPECT_EQ(res.ordered[0], &manifest_a);
    EXPECT_EQ(res.ordered[1], &manifest_b);
  } else {
    EXPECT_EQ(res.ordered[0], &manifest_b);
    EXPECT_EQ(res.ordered[1], &manifest_a);
  }
}

INSTANTIATE_TEST_SUITE_P(SecurityVersionCases, ManifestOrderTest,
                         testing::Values(
                             ManifestOrderTestCase{
                                 .primary = kBootSlotA,
                             },
                             ManifestOrderTestCase{
                                 .primary = kBootSlotB,
                             }));
}  // namespace
}  // namespace manifest_unittest
