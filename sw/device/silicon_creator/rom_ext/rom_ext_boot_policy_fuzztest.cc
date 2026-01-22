// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "fuzztest/fuzztest.h"
#include "gtest/gtest.h"
#include "sw/device/silicon_creator/rom_ext/rom_ext_boot_policy.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace boot_policy_fuzztest {
namespace {
using ::testing::_;
using ::testing::DoAll;
using ::testing::Each;
using ::testing::Return;
using ::testing::SetArgPointee;

using ::fuzztest::Arbitrary;
using ::fuzztest::ArrayOf;
using ::fuzztest::ElementOf;

/**
 * The `rom_ext_boot_policy_manifest_check` method has the following fields:
 * - `const manifest_t *manifest`
 * - `const boot_data_t *boot_data``
 *
 * This test ensures that the method never crashes, regardless of input.
 */
void ManifestCheckNeverCrashes(const std::vector<uint8_t> &manifest_data,
                               uint32_t length, uint32_t signed_region_end,
                               uint32_t code_start, uint32_t code_end,
                               uint32_t entry_point) {
  // Required Data
  manifest_t *manifest = (manifest_t *)manifest_data.data();
  manifest->identifier = CHIP_BL0_IDENTIFIER;
  manifest->length = length;
  manifest->security_version = 1;

  manifest->manifest_version.major = kManifestVersionMajor2;

  manifest->signed_region_end = signed_region_end;
  manifest->code_start = code_start;
  manifest->code_end = code_end;
  manifest->entry_point = entry_point;

  boot_data_t boot_data{};
  boot_data.min_security_version_bl0 = 0;

  // Execute Function

  [[maybe_unused]] rom_error_t error =
      rom_ext_boot_policy_manifest_check(manifest, &boot_data);
}

FUZZ_TEST(BootPolicyFuzzTest, ManifestCheckNeverCrashes)
    .WithDomains(fuzztest::VectorOf(fuzztest::Arbitrary<uint8_t>())
                     .WithSize(CHIP_MANIFEST_SIZE),
                 fuzztest::InRange(CHIP_BL0_SIZE_MIN, CHIP_BL0_SIZE_MAX),
                 Arbitrary<uint32_t>(), Arbitrary<uint32_t>(),
                 Arbitrary<uint32_t>(), Arbitrary<uint32_t>());
}  // namespace
}  // namespace boot_policy_fuzztest
