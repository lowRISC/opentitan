// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/mask_rom/boot_policy.h"

#include "gtest/gtest.h"
#include "sw/device/silicon_creator/lib/mock_manifest.h"
#include "sw/device/silicon_creator/mask_rom/mock_boot_policy_ptrs.h"
#include "sw/device/silicon_creator/testing/mask_rom_test.h"

namespace manifest_unittest {
namespace {
using ::testing::Return;

class BootPolicyTest : public mask_rom_test::MaskRomTest {
 protected:
  mask_rom_test::MockBootPolicyPtrs boot_policy_ptrs_;
  mask_rom_test::MockManifest mock_manifest_;
};

TEST_F(BootPolicyTest, ManifestCheck) {
  manifest_t manifest{};
  manifest.identifier = kBootPolicyRomExtIdentifier;

  EXPECT_CALL(mock_manifest_, Check(&manifest)).WillOnce(Return(kErrorOk));

  EXPECT_EQ(boot_policy_manifest_check(&manifest), kErrorOk);
}

TEST_F(BootPolicyTest, ManifestCheckOutOfBounds) {
  manifest_t manifest{};

  EXPECT_CALL(mock_manifest_, Check(&manifest))
      .WillOnce(Return(kErrorManifestBadLength));

  EXPECT_EQ(boot_policy_manifest_check(&manifest), kErrorManifestBadLength);
}

TEST_F(BootPolicyTest, ManifestCheckBadIdentifier) {
  manifest_t manifest{};

  EXPECT_CALL(mock_manifest_, Check(&manifest)).WillOnce(Return(kErrorOk));

  EXPECT_EQ(boot_policy_manifest_check(&manifest),
            kErrorBootPolicyBadIdentifier);
}

struct ManifestOrderTestCase {
  uint32_t version_a;
  uint32_t version_b;
  bool is_a_first;
};

class ManifestOrderTest
    : public BootPolicyTest,
      public testing::WithParamInterface<ManifestOrderTestCase> {};

TEST_P(ManifestOrderTest, ManifestsGet) {
  manifest_t manifest_a{};
  manifest_t manifest_b{};
  manifest_a.security_version = GetParam().version_a;
  manifest_b.security_version = GetParam().version_b;

  EXPECT_CALL(boot_policy_ptrs_, ManifestA).WillOnce(Return(&manifest_a));
  EXPECT_CALL(boot_policy_ptrs_, ManifestB).WillOnce(Return(&manifest_b));

  boot_policy_manifests_t res = boot_policy_manifests_get();
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
