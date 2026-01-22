// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "fuzztest/fuzztest.h"
#include "gtest/gtest.h"
#include "sw/device/silicon_creator/lib/drivers/mock_flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/mock_hmac.h"
#include "sw/device/silicon_creator/lib/drivers/mock_lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/mock_otp.h"
#include "sw/device/silicon_creator/lib/drivers/mock_rnd.h"
#include "sw/device/silicon_creator/lib/mock_boot_data.h"
#include "sw/device/silicon_creator/lib/mock_manifest.h"
#include "sw/device/silicon_creator/lib/ownership/mock_owner_verify.h"
#include "sw/device/silicon_creator/rom_ext/rom_ext_verify.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace verify_fuzztest {
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
 * The `rom_ext_verify` method has the following fields:
 * - ...
 *
 * This test ensures that the method never crashes, regardless of input.
 */
void VerifyNeverCrashes(const std::vector<uint8_t> &manifest_data,
                        uint32_t length, uint32_t signed_region_end,
                        uint32_t code_start, uint32_t code_end,
                        uint32_t entry_point) {
  // Required Data
  boot_data_t boot_data{};
  uint32_t flash_exec;
  owner_application_keyring_t keyring{};
  size_t verify_key;
  owner_config_t owner_config{};
  uint32_t isfb_check_count;

  // Manifest Config
  manifest_t *manifest = (manifest_t *)manifest_data.data();
  manifest->identifier = CHIP_BL0_IDENTIFIER;
  manifest->length = length;
  manifest->security_version = 1;

  manifest->manifest_version.major = kManifestVersionMajor2;

  manifest->signed_region_end = signed_region_end;
  manifest->code_start = code_start;
  manifest->code_end = code_end;
  manifest->entry_point = entry_point;

  manifest_ext_spx_key_t spx_key = {.key{.data = {0}}};

  // Boot Data Config
  boot_data.min_security_version_bl0 = 0;

  // Mock Config

  rom_test::NiceMockHmac mock_hmac_;
  rom_test::NiceMockManifest mock_manifest_;
  rom_test::NiceMockBootData mock_boot_data_;
  rom_test::NiceMockLifecycle mock_lifecycle_;
  rom_test::NiceMockOwnerVerify mock_owner_verify_;
  rom_test::NiceMockRnd mock_rnd_;
  rom_test::NiceMockOtp mock_otp_;

  ON_CALL(mock_manifest_, SpxKey)
      .WillByDefault(DoAll(SetArgPointee<1>(&spx_key), Return(kErrorOk)));

  ON_CALL(mock_manifest_, SpxSignature).WillByDefault(Return(kErrorOk));

  ON_CALL(mock_owner_verify_, verify).WillByDefault(Return(kErrorOk));

  ON_CALL(mock_boot_data_, Write).WillByDefault(Return(kErrorOk));
  ON_CALL(mock_boot_data_, Read).WillByDefault(Return(kErrorOk));

  // Execute Function

  [[maybe_unused]] rom_error_t error =
      rom_ext_verify(manifest, &boot_data, &flash_exec, &keyring, &verify_key,
                     &owner_config, &isfb_check_count);
}

FUZZ_TEST(VerifyFuzzTest, VerifyNeverCrashes)
    .WithDomains(fuzztest::VectorOf(fuzztest::Arbitrary<uint8_t>())
                     .WithSize(CHIP_MANIFEST_SIZE),
                 fuzztest::InRange(CHIP_BL0_SIZE_MIN, CHIP_BL0_SIZE_MAX),
                 Arbitrary<uint32_t>(), Arbitrary<uint32_t>(),
                 Arbitrary<uint32_t>(), Arbitrary<uint32_t>());
}  // namespace
}  // namespace verify_fuzztest
