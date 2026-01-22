// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "fuzztest/fuzztest.h"
#include "gtest/gtest.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/testing/binary_blob.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/drivers/mock_flash_ctrl.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/ownership/datatypes.h"
#include "sw/device/silicon_creator/lib/ownership/owner_block.h"
#include "sw/device/silicon_creator/lib/ownership/testdata/basic_owner_testdata.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace owner_block_fuzztest {
namespace {

using rom_test::FlashCfg;
using rom_test::FlashInfoPage;
using rom_test::FlashPerms;
using rom_test::MockFlashCtrl;

using ::testing::_;
using ::testing::DoAll;
using ::testing::Each;
using ::testing::Return;
using ::testing::SetArgPointee;

using ::testutil::BinaryBlob;

using ::fuzztest::Arbitrary;
using ::fuzztest::ArrayOf;
using ::fuzztest::ElementOf;

/**
 * The `owner_block_parse` method has the following parameters:
 * - `const owner_block_t *block`
 * - `hardened_bool_t check_only`
 * - `owner_config_t *config`
 * - `owner_application_keyring_t *keyring`
 *
 * This test ensures that the parser never crashes, regardless of input.
 */
void ParserNeverCrashes(const std::vector<uint8_t> &owner_block_data) {
  // Required Data
  BinaryBlob<owner_block_t> block(owner_block_data.data(),
                                  sizeof(owner_block_data.data()));
  owner_config_t config;
  owner_application_keyring_t keyring{};

  // Required Mocks
  MockFlashCtrl mock_flash_ctrl_;

  // Flash Config

  flash_ctrl_cfg_t default_config = {
      .scrambling = kMultiBitBool4False,
      .ecc = kMultiBitBool4False,
      .he = kMultiBitBool4False,
  };

  ON_CALL(mock_flash_ctrl_, DataDefaultCfgGet)
      .WillByDefault(Return(default_config));

  // Execute Function

  [[maybe_unused]] rom_error_t error =
      owner_block_parse(block.get(),
                        /*check_only=*/kHardenedBoolFalse, &config, &keyring);
}

/**
 * The `owner_block_info_apply` method has the following parameters:
 * - `const owner_flash_info_config_t *info`
 *
 * This test ensures that the method never crashes, regardless of input.
 */
void OwnerBlockInfoApplyNeverCrashes(uint32_t header_tag,
                                     uint16_t header_length,
                                     uint8_t major_version,
                                     uint8_t minor_version) {
  // Required Data
  owner_flash_info_config_t info = {.header = {.tag = header_tag,
                                               .length = header_length,
                                               .version = {
                                                   .major = major_version,
                                                   .minor = minor_version,
                                               }}};

  // Execute Function
  [[maybe_unused]] rom_error_t error = owner_block_info_apply(&info);
}

/**
 * The `owner_block_info_lockdown` method has the following parameters:
 * - `const owner_flash_info_config_t *info`
 *
 * This test ensures that the method never crashes, regardless of input.
 */
void OwnerBlockInfoLockdownNeverCrashes(uint32_t header_tag,
                                        uint16_t header_length,
                                        uint8_t major_version,
                                        uint8_t minor_version) {
  // Required Data
  owner_flash_info_config_t info = {.header = {.tag = header_tag,
                                               .length = header_length,
                                               .version = {
                                                   .major = major_version,
                                                   .minor = minor_version,
                                               }}};

  // Execute Function
  [[maybe_unused]] rom_error_t error = owner_block_info_lockdown(&info);
}

/**
 * The `owner_block_info_isfb_erase_enable` method has the following parameters:
 * - `boot_data_t *bootdata`
 * - `const owner_flash_info_config_t *owner_config`
 *
 * This test ensures that the method never crashes, regardless of input.
 */
void OwnerBlockInfoIsfbEraseEnableNeverCrashes(uint32_t header_tag,
                                               uint16_t header_length,
                                               uint8_t major_version,
                                               uint8_t minor_version) {
  // Required Data
  boot_data_t bootdata = {
      .ownership_state = kOwnershipStateLockedOwner,

  };

  const owner_isfb_config_t isfb_config = {
      .header = {.tag = header_tag,
                 .length = header_length,
                 .version = {
                     .major = major_version,
                     .minor = minor_version,
                 }}};

  owner_config_t owner_config = {.isfb = &isfb_config};

  // Execute Function
  [[maybe_unused]] rom_error_t error =
      owner_block_info_isfb_erase_enable(&bootdata, &owner_config);
}

/**
 * The `owner_block_flash_check` method has the following parameters:
 * - `const owner_flash_config_t *flash`
 *
 * This test ensures that the method never crashes, regardless of input.
 */
void OwnerBlockFlashCheckNeverCrashes(uint32_t header_tag,
                                      uint16_t header_length,
                                      uint8_t major_version,
                                      uint8_t minor_version) {
  // Required Data
  owner_flash_config_t flash = {.header = {.tag = header_tag,
                                           .length = header_length,
                                           .version = {
                                               .major = major_version,
                                               .minor = minor_version,
                                           }}};

  // Execute Function
  [[maybe_unused]] rom_error_t error = owner_block_flash_check(&flash);
}

/**
 * The `owner_rescue_command_allowed` method has the following parameters:
 * - `const owner_rescue_config_t *rescue`
 * - `uint32_t command`
 *
 * This test ensures that the method never crashes, regardless of input.
 */
void OwnerRescueCommandAllowedNeverCrashes(uint32_t header_tag,
                                           uint16_t header_length,
                                           uint8_t major_version,
                                           uint8_t minor_version,
                                           uint32_t command) {
  // Required Data
  owner_rescue_config_t rescue = {.header = {.tag = header_tag,
                                             .length = header_length,
                                             .version = {
                                                 .major = major_version,
                                                 .minor = minor_version,
                                             }}};

  // Execute Function
  [[maybe_unused]] hardened_bool_t result =
      owner_rescue_command_allowed(&rescue, command);
}

FUZZ_TEST(OwnerBlockFuzzTest, ParserNeverCrashes)
    .WithDomains(
        fuzztest::VectorOf(fuzztest::Arbitrary<uint8_t>()).WithSize(2048));

// The following fuzz tests all will crash due to length arguments.
// However, the crashes aren't "real" as the calling function is expected to
// have verified length beforehand. FUZZ_TEST(OwnerBlockFuzzTest,
// OwnerBlockInfoApplyNeverCrashes); FUZZ_TEST(OwnerBlockFuzzTest,
// OwnerBlockInfoLockdownNeverCrashes); FUZZ_TEST(OwnerBlockFuzzTest,
// OwnerBlockInfoIsfbEraseEnableNeverCrashes); FUZZ_TEST(OwnerBlockFuzzTest,
// OwnerBlockFlashCheckNeverCrashes); FUZZ_TEST(OwnerBlockFuzzTest,
// OwnerRescueCommandAllowedNeverCrashes);
}  // namespace
}  // namespace owner_block_fuzztest
