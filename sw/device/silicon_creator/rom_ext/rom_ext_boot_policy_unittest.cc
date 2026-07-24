// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom_ext/rom_ext_boot_policy.h"

#include <cstring>
#include <sys/mman.h>

#include "gtest/gtest.h"
#include "sw/device/silicon_creator/lib/mock_boot_data.h"
#include "sw/device/silicon_creator/lib/mock_manifest.h"
#include "sw/device/silicon_creator/rom_ext/mock_rom_ext_boot_policy_ptrs.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

extern "C" {
char _owner_virtual_start_address[1] = {0};
}

namespace manifest_unittest {
namespace {
using ::testing::_;
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
  boot_data.identifier = kBootDataIdentifier;

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
  boot_data.identifier = kBootDataIdentifier;
  manifest_t manifest{};

  EXPECT_EQ(rom_ext_boot_policy_manifest_check(&manifest, &boot_data),
            kErrorBootPolicyBadIdentifier);
}

TEST_F(RomExtBootPolicyTest, ManifestCheckBadLength) {
  boot_data_t boot_data{};
  boot_data.identifier = kBootDataIdentifier;
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
  boot_data.identifier = kBootDataIdentifier;
  boot_data.min_security_version_bl0 = 1;

  manifest_t manifest{};
  manifest.identifier = CHIP_BL0_IDENTIFIER;
  manifest.length = CHIP_BL0_SIZE_MIN;
  manifest.security_version = 0;

  EXPECT_EQ(rom_ext_boot_policy_manifest_check(&manifest, &boot_data),
            kErrorBootPolicyRollback);
}

TEST_F(RomExtBootPolicyTest, ManifestCheckBadSignedRegion) {
  boot_data_t boot_data{};
  boot_data.identifier = kBootDataIdentifier;
  boot_data.min_security_version_bl0 = 1;

  manifest_t manifest{};
  manifest.identifier = CHIP_BL0_IDENTIFIER;
  manifest.length = CHIP_BL0_SIZE_MIN;
  manifest.security_version = 1;
  manifest.manifest_version.major = kManifestVersionMajor2;
  manifest.signed_region_end = manifest.length + 1;

  EXPECT_EQ(rom_ext_boot_policy_manifest_check(&manifest, &boot_data),
            kErrorManifestBadSignedRegion);
}

TEST_F(RomExtBootPolicyTest, ManifestCheckBadEntryPoint) {
  boot_data_t boot_data{};
  boot_data.identifier = kBootDataIdentifier;
  boot_data.min_security_version_bl0 = 1;

  manifest_t manifest{};
  manifest.identifier = CHIP_BL0_IDENTIFIER;
  manifest.length = sizeof(manifest_t) + 0x1000;
  manifest.security_version = 1;
  manifest.manifest_version.major = kManifestVersionMajor2;
  manifest.signed_region_end = sizeof(manifest_t) + 0x900;
  manifest.code_start = sizeof(manifest_t);
  manifest.code_end = sizeof(manifest_t) + 0x800;
  manifest.entry_point = manifest.code_start - 1;

  EXPECT_EQ(rom_ext_boot_policy_manifest_check(&manifest, &boot_data),
            kErrorManifestBadEntryPoint);
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

  EXPECT_CALL(rom_ext_boot_policy_ptrs_, ManifestA())
      .WillOnce(Return(&manifest_a));
  EXPECT_CALL(rom_ext_boot_policy_ptrs_, ManifestB())
      .WillOnce(Return(&manifest_b));

  boot_data_t boot_data{};
  boot_data.identifier = kBootDataIdentifier;
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

class RomExtBootPolicySearchTest : public RomExtBootPolicyTest {
 protected:
  static constexpr size_t kLowOffset = 64 * 1024;
#ifdef OT_COVERAGE_ENABLED
  static constexpr size_t kHighOffset = 168 * 1024;
#else
  static constexpr size_t kHighOffset = 88 * 1024;
#endif
  static constexpr size_t kBufferSize = kHighOffset + sizeof(manifest_t);

  void SetUp() override {
    RomExtBootPolicyTest::SetUp();
    // Allocate buffer using mmap with MAP_32BIT rather than standard heap
    // allocators (such as malloc/new) to guarantee the buffer resides within
    // the 32-bit address space required by 32-bit target manifest pointers
    // (such as manifest_base_address).
    buffer_ = (uint8_t *)mmap(NULL, kBufferSize, PROT_READ | PROT_WRITE,
                              MAP_PRIVATE | MAP_ANONYMOUS | MAP_32BIT, -1, 0);
    ASSERT_NE(buffer_, MAP_FAILED);
    std::memset(buffer_, 0x5a, kBufferSize);
  }

  void TearDown() override {
    munmap(buffer_, kBufferSize);
    RomExtBootPolicyTest::TearDown();
  }

  void InitManifest(manifest_t *manifest) {
    manifest->identifier = CHIP_BL0_IDENTIFIER;
    manifest->length = sizeof(manifest_t) + 0x1000;
    manifest->security_version = 1;
    manifest->manifest_version.major = kManifestVersionMajor2;
    manifest->signed_region_end = sizeof(manifest_t) + 0x900;
    manifest->code_start = sizeof(manifest_t);
    manifest->code_end = sizeof(manifest_t) + 0x800;
    manifest->entry_point = sizeof(manifest_t) + 0x100;
    manifest->manifest_base_address = (uint32_t)(uintptr_t)manifest;
  }

  uint8_t *buffer_;
};

TEST_F(RomExtBootPolicySearchTest, NoManifests) {
  boot_data_t boot_data{};
  boot_data.identifier = kBootDataIdentifier;

  uintptr_t bank_base = (uintptr_t)buffer_;
  rom_error_t status = kErrorOk;
  const manifest_t *result =
      rom_ext_boot_policy_manifest_bank_search(bank_base, &boot_data, &status);
  EXPECT_EQ(result, (const manifest_t *)(bank_base + kLowOffset));
}

TEST_F(RomExtBootPolicySearchTest, ValidManifestAtLowOffset) {
  boot_data_t boot_data{};
  boot_data.identifier = kBootDataIdentifier;

  uintptr_t bank_base = (uintptr_t)buffer_;
  manifest_t *manifest = (manifest_t *)(buffer_ + kLowOffset);
  InitManifest(manifest);

  rom_error_t status = kErrorOk;
  const manifest_t *result =
      rom_ext_boot_policy_manifest_bank_search(bank_base, &boot_data, &status);
  EXPECT_EQ(result, manifest);
}

TEST_F(RomExtBootPolicySearchTest, ValidManifestAtHighOffset) {
  boot_data_t boot_data{};
  boot_data.identifier = kBootDataIdentifier;

  uintptr_t bank_base = (uintptr_t)buffer_;
  manifest_t *manifest = (manifest_t *)(buffer_ + kHighOffset);
  InitManifest(manifest);

  rom_error_t status = kErrorOk;
  const manifest_t *result =
      rom_ext_boot_policy_manifest_bank_search(bank_base, &boot_data, &status);
  EXPECT_EQ(result, manifest);
}

TEST_F(RomExtBootPolicySearchTest, MultipleValidManifestsPrefersHighestOffset) {
  boot_data_t boot_data{};
  boot_data.identifier = kBootDataIdentifier;

  uintptr_t bank_base = (uintptr_t)buffer_;
  manifest_t *manifest_low = (manifest_t *)(buffer_ + kLowOffset);
  manifest_t *manifest_high = (manifest_t *)(buffer_ + kHighOffset);
  InitManifest(manifest_low);
  InitManifest(manifest_high);

  rom_error_t status = kErrorOk;
  const manifest_t *result =
      rom_ext_boot_policy_manifest_bank_search(bank_base, &boot_data, &status);
  EXPECT_EQ(result, manifest_high);
}

TEST_F(RomExtBootPolicySearchTest, InvalidManifestAtHighOffsetValidAtLow) {
  boot_data_t boot_data{};
  boot_data.identifier = kBootDataIdentifier;

  uintptr_t bank_base = (uintptr_t)buffer_;
  manifest_t *manifest_high = (manifest_t *)(buffer_ + kHighOffset);
  manifest_t *manifest_low = (manifest_t *)(buffer_ + kLowOffset);
  InitManifest(manifest_high);
  manifest_high->manifest_base_address = 0;  // Invalid base address
  InitManifest(manifest_low);

  rom_error_t status = kErrorOk;
  const manifest_t *result =
      rom_ext_boot_policy_manifest_bank_search(bank_base, &boot_data, &status);
  EXPECT_EQ(result, manifest_low);
}

TEST_F(RomExtBootPolicySearchTest, InvalidManifestAtHighOffsetOnly) {
  boot_data_t boot_data{};
  boot_data.identifier = kBootDataIdentifier;

  uintptr_t bank_base = (uintptr_t)buffer_;
  manifest_t *manifest = (manifest_t *)(buffer_ + kHighOffset);
  InitManifest(manifest);
  manifest->manifest_base_address = 0;  // Invalid base address

  rom_error_t status = kErrorOk;
  const manifest_t *result =
      rom_ext_boot_policy_manifest_bank_search(bank_base, &boot_data, &status);
  EXPECT_EQ(result, manifest);
}

}  // namespace
}  // namespace manifest_unittest
