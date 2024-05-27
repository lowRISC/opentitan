// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom/boot_policy.h"

#include "gtest/gtest.h"
#include "sw/device/silicon_creator/lib/base/chip.h"
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

struct ManifestLengthTestCase {
  uint32_t length;
  rom_error_t result;
};

class ManifestCheckLengthTest
    : public BootPolicyTest,
      public testing::WithParamInterface<ManifestLengthTestCase> {};

TEST_P(ManifestCheckLengthTest, ManifestCheckLength) {
  manifest_t manifest{};
  manifest.identifier = CHIP_ROM_EXT_IDENTIFIER;
  manifest.length = GetParam().length;
  boot_data_t boot_data{};

  if (GetParam().result == kErrorOk) {
    EXPECT_CALL(mock_manifest_, Check(&manifest)).WillOnce(Return(kErrorOk));
  }

  EXPECT_EQ(boot_policy_manifest_check(&manifest, &boot_data),
            GetParam().result);
}

INSTANTIATE_TEST_SUITE_P(
    GoodLengths, ManifestCheckLengthTest,
    testing::Values(
        ManifestLengthTestCase{CHIP_ROM_EXT_SIZE_MIN, kErrorOk},
        ManifestLengthTestCase{CHIP_ROM_EXT_SIZE_MAX >> 1, kErrorOk},
        ManifestLengthTestCase{CHIP_ROM_EXT_SIZE_MAX, kErrorOk},
        ManifestLengthTestCase{CHIP_ROM_EXT_RESIZABLE_SIZE_MAX, kErrorOk},
        ManifestLengthTestCase{CHIP_ROM_EXT_SIZE_MIN - 1,
                               kErrorBootPolicyBadLength},
        ManifestLengthTestCase{CHIP_ROM_EXT_RESIZABLE_SIZE_MAX + 1,
                               kErrorBootPolicyBadLength}));

TEST_F(BootPolicyTest, ManifestCheckBadIdentifier) {
  manifest_t manifest{};
  boot_data_t boot_data{};

  EXPECT_EQ(boot_policy_manifest_check(&manifest, &boot_data),
            kErrorBootPolicyBadIdentifier);
}

TEST_F(BootPolicyTest, ManifestCheckBadManifest) {
  manifest_t manifest{};
  manifest.identifier = CHIP_ROM_EXT_IDENTIFIER;
  manifest.length = CHIP_ROM_EXT_SIZE_MAX;
  boot_data_t boot_data{};

  EXPECT_CALL(mock_manifest_, Check(&manifest))
      .WillOnce(Return(kErrorManifestBadEntryPoint));
  EXPECT_EQ(boot_policy_manifest_check(&manifest, &boot_data),
            kErrorManifestBadEntryPoint);
}

TEST_F(BootPolicyTest, ManifestCheckRollback) {
  manifest_t manifest{};
  manifest.identifier = CHIP_ROM_EXT_IDENTIFIER;
  manifest.length = CHIP_ROM_EXT_SIZE_MAX;
  boot_data_t boot_data{};
  boot_data.min_security_version_rom_ext = 1;

  EXPECT_CALL(mock_manifest_, Check(&manifest)).WillOnce(Return(kErrorOk));
  EXPECT_EQ(boot_policy_manifest_check(&manifest, &boot_data),
            kErrorBootPolicyRollback);
}

struct Versions {
  uint32_t security;
  uint32_t major;
  uint32_t minor;
};

struct ManifestOrderTestCase {
  Versions version_a;
  Versions version_b;
  bool is_a_first;
};

class ManifestOrderTest
    : public BootPolicyTest,
      public testing::WithParamInterface<ManifestOrderTestCase> {};

TEST_P(ManifestOrderTest, ManifestsGet) {
  const ManifestOrderTestCase &param = GetParam();
  manifest_t manifest_a{
      .version_major = param.version_a.major,
      .version_minor = param.version_a.minor,
      .security_version = param.version_a.security,
  };
  manifest_t manifest_b{
      .version_major = param.version_b.major,
      .version_minor = param.version_b.minor,
      .security_version = param.version_b.security,
  };

  EXPECT_CALL(boot_policy_ptrs_, ManifestA).WillOnce(Return(&manifest_a));
  EXPECT_CALL(boot_policy_ptrs_, ManifestB).WillOnce(Return(&manifest_b));

  boot_policy_manifests_t res = boot_policy_manifests_get();
  if (param.is_a_first) {
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
        // Versions equal, choose A.
        ManifestOrderTestCase{
            .version_a = {0, 0, 0},
            .version_b = {0, 0, 0},
            .is_a_first = true,
        },
        // A.secver > B.secver, choose A.
        ManifestOrderTestCase{
            .version_a = {1, 0, 0},
            .version_b = {0, 0, 0},
            .is_a_first = true,
        },
        // A.secver < B.secver, choose B.
        ManifestOrderTestCase{
            .version_a = {0, 0, 0},
            .version_b = {1, 0, 0},
            .is_a_first = false,
        },
        // Secver equal, A.major > B.major, choose A.
        ManifestOrderTestCase{
            .version_a = {0, 1, 0},
            .version_b = {0, 0, 0},
            .is_a_first = true,
        },
        // Secver equal, B.major > A.major, choose B.
        ManifestOrderTestCase{
            .version_a = {0, 1, 0},
            .version_b = {0, 2, 0},
            .is_a_first = false,
        },
        // Secver equal, major equal, A.minor > B.minor, choose A.
        ManifestOrderTestCase{
            .version_a = {0, 3, 1},
            .version_b = {0, 3, 0},
            .is_a_first = true,
        },
        // Secver equal, major equal, A.minor < B.minor, choose B.
        ManifestOrderTestCase{
            .version_a = {0, 3, 1},
            .version_b = {0, 3, 5},
            .is_a_first = false,
        },
        // Signed integer limit wraparound. B is larger; choose B.
        ManifestOrderTestCase{
            .version_a = {std::numeric_limits<int32_t>::max(), 0, 0},
            .version_b =
                {static_cast<uint32_t>(std::numeric_limits<int32_t>::max()) + 1,
                 0, 0},
            .is_a_first = false,
        }));

}  // namespace
}  // namespace manifest_unittest
