// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom/boot_policy.h"

#include "gtest/gtest.h"
#include "sw/device/silicon_creator/lib/mock_manifest.h"
#include "sw/device/silicon_creator/lib/mock_shutdown.h"
#include "sw/device/silicon_creator/rom/mock_boot_policy_ptrs.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace manifest_unittest {
namespace {
using ::testing::Return;

class BootPolicyTest : public rom_test::RomTest {
 protected:
  rom_test::MockBootPolicyPtrs boot_policy_ptrs_;
  rom_test::MockManifest mock_manifest_;
};

class ManifestCheckLengthTest : public BootPolicyTest,
                                public testing::WithParamInterface<uint32_t> {};

TEST_P(ManifestCheckLengthTest, ManifestCheckGood) {
  manifest_t manifest{};
  manifest.identifier = MANIFEST_IDENTIFIER_ROM_EXT;
  manifest.length = GetParam();
  boot_data_t boot_data{};

  EXPECT_CALL(mock_manifest_, Check(&manifest)).WillOnce(Return(kErrorOk));

  EXPECT_EQ(boot_policy_manifest_check(&manifest, &boot_data), kErrorOk);
}

INSTANTIATE_TEST_SUITE_P(GoodLengths, ManifestCheckLengthTest,
                         testing::Values(MANIFEST_LENGTH_FIELD_ROM_EXT_MIN,
                                         MANIFEST_LENGTH_FIELD_ROM_EXT_MAX >> 1,
                                         MANIFEST_LENGTH_FIELD_ROM_EXT_MAX));

TEST_F(BootPolicyTest, ManifestCheckBadIdentifier) {
  manifest_t manifest{};
  boot_data_t boot_data{};

  EXPECT_EQ(boot_policy_manifest_check(&manifest, &boot_data),
            kErrorBootPolicyBadIdentifier);
}

TEST_F(BootPolicyTest, ManifestCheckBadLength) {
  manifest_t manifest{};
  manifest.identifier = MANIFEST_IDENTIFIER_ROM_EXT;
  boot_data_t boot_data{};

  manifest.length = MANIFEST_LENGTH_FIELD_ROM_EXT_MIN - 1;
  EXPECT_EQ(boot_policy_manifest_check(&manifest, &boot_data),
            kErrorBootPolicyBadLength);

  manifest.length = MANIFEST_LENGTH_FIELD_ROM_EXT_MAX + 1;
  EXPECT_EQ(boot_policy_manifest_check(&manifest, &boot_data),
            kErrorBootPolicyBadLength);
}

TEST_F(BootPolicyTest, ManifestCheckBadManifest) {
  manifest_t manifest{};
  manifest.identifier = MANIFEST_IDENTIFIER_ROM_EXT;
  manifest.length = MANIFEST_LENGTH_FIELD_ROM_EXT_MAX;
  boot_data_t boot_data{};

  EXPECT_CALL(mock_manifest_, Check(&manifest))
      .WillOnce(Return(kErrorManifestBadEntryPoint));
  EXPECT_EQ(boot_policy_manifest_check(&manifest, &boot_data),
            kErrorManifestBadEntryPoint);
}

TEST_F(BootPolicyTest, ManifestCheckRollback) {
  manifest_t manifest{};
  manifest.identifier = MANIFEST_IDENTIFIER_ROM_EXT;
  manifest.length = MANIFEST_LENGTH_FIELD_ROM_EXT_MAX;
  boot_data_t boot_data{};
  boot_data.min_security_version_rom_ext = 1;

  EXPECT_CALL(mock_manifest_, Check(&manifest)).WillOnce(Return(kErrorOk));
  EXPECT_EQ(boot_policy_manifest_check(&manifest, &boot_data),
            kErrorBootPolicyRollback);
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
