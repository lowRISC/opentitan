// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom_ext/rom_ext_boot_policy.h"

#include "gtest/gtest.h"
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
};

TEST_F(RomExtBootPolicyTest, ManifestCheck) {
  manifest_t manifest{};
  manifest.identifier = CHIP_BL0_IDENTIFIER;

  manifest.length = CHIP_BL0_SIZE_MIN;
  EXPECT_CALL(mock_manifest_, Check(&manifest)).WillOnce(Return(kErrorOk));
  EXPECT_EQ(rom_ext_boot_policy_manifest_check(&manifest), kErrorOk);

  manifest.length = CHIP_BL0_SIZE_MAX >> 1;
  EXPECT_CALL(mock_manifest_, Check(&manifest)).WillOnce(Return(kErrorOk));
  EXPECT_EQ(rom_ext_boot_policy_manifest_check(&manifest), kErrorOk);

  manifest.length = CHIP_BL0_SIZE_MAX;
  EXPECT_CALL(mock_manifest_, Check(&manifest)).WillOnce(Return(kErrorOk));
  EXPECT_EQ(rom_ext_boot_policy_manifest_check(&manifest), kErrorOk);
}

TEST_F(RomExtBootPolicyTest, ManifestCheckBadIdentifier) {
  manifest_t manifest{};

  EXPECT_EQ(rom_ext_boot_policy_manifest_check(&manifest),
            kErrorBootPolicyBadIdentifier);
}

TEST_F(RomExtBootPolicyTest, ManifestCheckBadLength) {
  manifest_t manifest{};
  manifest.identifier = CHIP_BL0_IDENTIFIER;

  manifest.length = CHIP_BL0_SIZE_MIN - 1;
  EXPECT_EQ(rom_ext_boot_policy_manifest_check(&manifest),
            kErrorBootPolicyBadLength);

  manifest.length = CHIP_BL0_SIZE_MAX + 1;
  EXPECT_EQ(rom_ext_boot_policy_manifest_check(&manifest),
            kErrorBootPolicyBadLength);
}

struct ManifestOrderTestCase {
  uint32_t version_a;
  uint32_t version_b;
  bool is_a_first;
};

class ManifestOrderTest
    : public RomExtBootPolicyTest,
      public testing::WithParamInterface<ManifestOrderTestCase> {};

TEST_P(ManifestOrderTest, ManifestsGet) {
  manifest_t manifest_a{};
  manifest_t manifest_b{};
  manifest_a.security_version = GetParam().version_a;
  manifest_b.security_version = GetParam().version_b;

  EXPECT_CALL(rom_ext_boot_policy_ptrs_, ManifestA)
      .WillOnce(Return(&manifest_a));
  EXPECT_CALL(rom_ext_boot_policy_ptrs_, ManifestB)
      .WillOnce(Return(&manifest_b));

  rom_ext_boot_policy_manifests_t res = rom_ext_boot_policy_manifests_get();
  if (GetParam().is_a_first) {
    EXPECT_EQ(res.ordered[0], &manifest_a);
    EXPECT_EQ(res.ordered[1], &manifest_b);
  } else {
    EXPECT_EQ(res.ordered[0], &manifest_b);
    EXPECT_EQ(res.ordered[1], &manifest_a);
  }
}

INSTANTIATE_TEST_SUITE_P(
    SecurityVersionCases, ManifestOrderTest,
    testing::Values(
        ManifestOrderTestCase{
            .version_a = 0,
            .version_b = 0,
            .is_a_first = true,
        },
        ManifestOrderTestCase{
            .version_a = 1,
            .version_b = 0,
            .is_a_first = true,
        },
        ManifestOrderTestCase{
            .version_a = 0,
            .version_b = 1,
            .is_a_first = false,
        },
        ManifestOrderTestCase{
            .version_a = std::numeric_limits<int32_t>::max(),
            .version_b =
                static_cast<uint32_t>(std::numeric_limits<int32_t>::max()) + 1,
            .is_a_first = false,
        }));

}  // namespace
}  // namespace manifest_unittest
