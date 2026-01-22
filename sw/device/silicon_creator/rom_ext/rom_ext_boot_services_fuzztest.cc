// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "fuzztest/fuzztest.h"
#include "gtest/gtest.h"
#include "sw/device/silicon_creator/lib/boot_svc/mock_boot_svc_header.h"
#include "sw/device/silicon_creator/lib/drivers/mock_flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/mock_hmac.h"
#include "sw/device/silicon_creator/lib/drivers/mock_lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/mock_otp.h"
#include "sw/device/silicon_creator/lib/drivers/mock_rnd.h"
#include "sw/device/silicon_creator/lib/mock_boot_data.h"
#include "sw/device/silicon_creator/lib/mock_manifest.h"
#include "sw/device/silicon_creator/lib/ownership/datatypes.h"
#include "sw/device/silicon_creator/lib/ownership/mock_owner_verify.h"
#include "sw/device/silicon_creator/lib/ownership/mock_ownership_key.h"
#include "sw/device/silicon_creator/lib/ownership/owner_block.h"
#include "sw/device/silicon_creator/lib/ownership/ownership_activate.h"
#include "sw/device/silicon_creator/rom_ext/mock_rom_ext_boot_policy_ptrs.h"
#include "sw/device/silicon_creator/rom_ext/rom_ext_boot_services.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace boot_services_fuzzest {
namespace {
using ::testing::_;
using ::testing::DoAll;
using ::testing::Each;
using ::testing::Return;
using ::testing::SetArgPointee;

using ::fuzztest::Arbitrary;
using ::fuzztest::ArrayOf;
using ::fuzztest::ElementOf;

void HandlerNeverCrashesHeader(uint32_t headerIdentifier, uint32_t headerType,
                               uint32_t headerLength, uint32_t hashDigest) {
  // Required Data
  boot_svc_msg_t boot_svc_msg{};
  boot_data_t boot_data{};
  boot_log_t boot_log{};
  lifecycle_state_t lc_state{};
  owner_application_keyring_t keyring{};
  size_t verify_key;
  owner_config_t owner_config{};
  uint32_t isfb_check_count;

  // Required Mocks
  rom_test::NiceMockHmac mock_hmac_;
  rom_test::NiceMockManifest mock_manifest_;
  rom_test::NiceMockBootData mock_boot_data_;
  rom_test::NiceMockLifecycle mock_lifecycle_;
  rom_test::NiceMockOwnerVerify mock_owner_verify_;
  rom_test::NiceMockRnd mock_rnd_;
  rom_test::NiceMockOwnershipKey mock_ownership_key_;
  rom_test::NiceMockRomExtBootPolicyPtrs mock_rom_ext_boot_policy_ptrs_;
  rom_test::NiceMockOtp mock_otp_;

  // Header Configuration
  boot_svc_msg.header.identifier = headerIdentifier;
  boot_svc_msg.header.type = headerType;
  boot_svc_msg.header.length = headerLength;
  boot_svc_msg.header.digest = hmac_digest_t{hashDigest};

  [[maybe_unused]] rom_error_t error =
      boot_svc_handler(&boot_svc_msg, &boot_data, &boot_log, lc_state, &keyring,
                       &verify_key, &owner_config, &isfb_check_count);
}

void HandlerNeverCrashesMessages(
    uint32_t headerType,
    const std::array<uint32_t, kBootSvcEmptyPayloadWordCount> &random_payload) {
  // Required Data
  boot_svc_msg_t boot_svc_msg{};
  boot_data_t boot_data{};
  boot_log_t boot_log{};
  lifecycle_state_t lc_state{};
  owner_application_keyring_t keyring{};
  size_t verify_key;
  owner_config_t owner_config{};
  uint32_t isfb_check_count;

  // Required Mocks
  rom_test::NiceMockHmac mock_hmac_;
  rom_test::NiceMockManifest mock_manifest_;
  rom_test::NiceMockBootData mock_boot_data_;
  rom_test::NiceMockLifecycle mock_lifecycle_;
  rom_test::NiceMockOwnerVerify mock_owner_verify_;
  rom_test::NiceMockRnd mock_rnd_;
  rom_test::NiceMockOwnershipKey mock_ownership_key_;
  rom_test::NiceMockRomExtBootPolicyPtrs mock_rom_ext_boot_policy_ptrs_;
  rom_test::NiceMockOtp mock_otp_;

  // Header Configuration
  boot_svc_msg.header.identifier = kBootSvcIdentifier;
  boot_svc_msg.header.type = headerType;
  boot_svc_msg.header.length = sizeof(boot_svc_empty_t);
  boot_svc_msg.header.digest = hmac_digest_t{0x1234};

  // Message Configuration
  memcpy(boot_svc_msg.empty.payload, random_payload.data(),
         sizeof(boot_svc_msg.empty.payload));

  // Boot Data Configuration
  boot_data.min_security_version_bl0 = 1;

  // Owner Configuration
  owner_config.isfb = (owner_isfb_config_t *)kHardenedBoolFalse;

  owner_application_key_t key = {
      .header =
          {
              .tag = kTlvTagApplicationKey,
              .length = sizeof(owner_application_key_t),
          },
      .key_alg = kOwnershipKeyAlgEcdsaP256,
  };

  // Keyring Configuration
  keyring.length = 1;
  keyring.key[0] = &key;

  // Manifest Configuration
  manifest_ext_spx_key_t spx_key = {.key{.data = {0}}};

  manifest_t manifest_a{};
  manifest_t manifest_b{};

  manifest_a.identifier = CHIP_BL0_IDENTIFIER;
  manifest_a.length = CHIP_BL0_SIZE_MIN;
  manifest_a.security_version = 1;
  manifest_a.manifest_version.major = kManifestVersionMajor2;
  manifest_a.length = sizeof(manifest_t) + 0x1000;
  manifest_a.signed_region_end = sizeof(manifest_t) + 0x900;
  manifest_a.code_start = sizeof(manifest_t);
  manifest_a.code_end = sizeof(manifest_t) + 0x800;
  manifest_a.entry_point = 0x500;
  manifest_a.ecdsa_public_key.x[0] = 0;

  manifest_b.identifier = CHIP_BL0_IDENTIFIER;
  manifest_b.length = CHIP_BL0_SIZE_MIN;
  manifest_b.security_version = 1;
  manifest_b.manifest_version.major = kManifestVersionMajor2;
  manifest_b.length = sizeof(manifest_t) + 0x1000;
  manifest_b.signed_region_end = sizeof(manifest_t) + 0x900;
  manifest_b.code_start = sizeof(manifest_t);
  manifest_b.code_end = sizeof(manifest_t) + 0x800;
  manifest_b.entry_point = 0x500;
  manifest_b.ecdsa_public_key.x[0] = 0;

  ON_CALL(mock_hmac_, sha256)
      .WillByDefault(SetArgPointee<2>(hmac_digest_t{0x1234}));

  ON_CALL(mock_rom_ext_boot_policy_ptrs_, ManifestA)
      .WillByDefault(Return(&manifest_a));

  ON_CALL(mock_rom_ext_boot_policy_ptrs_, ManifestB)
      .WillByDefault(Return(&manifest_b));

  ON_CALL(mock_manifest_, SpxKey)
      .WillByDefault(DoAll(SetArgPointee<1>(&spx_key), Return(kErrorOk)));

  ON_CALL(mock_manifest_, SpxSignature).WillByDefault(Return(kErrorOk));

  ON_CALL(mock_owner_verify_, verify).WillByDefault(Return(kErrorOk));

  ON_CALL(mock_boot_data_, Write).WillByDefault(Return(kErrorOk));
  ON_CALL(mock_boot_data_, Read).WillByDefault(Return(kErrorOk));

  ON_CALL(mock_ownership_key_, validate).WillByDefault(Return(kErrorOk));

  ON_CALL(mock_lifecycle_, DeviceId)
      .WillByDefault(SetArgPointee<0>((lifecycle_device_id_t){0}));

  ON_CALL(mock_rnd_, Uint32).WillByDefault(Return(5));

  [[maybe_unused]] rom_error_t error =
      boot_svc_handler(&boot_svc_msg, &boot_data, &boot_log, lc_state, &keyring,
                       &verify_key, &owner_config, &isfb_check_count);
}

/**
 * The `header` message has the following fields:
 * - `hmac_digest_t digest`
 * - `uint32_t identifier`
 * - `uint32_t type`
 * - `uint32_t length`
 *
 * All `identifier` values except `kBootSvcIdentifier` should
 * be ignored and return `kErrorOk`.
 */
void HeaderIdentifier(uint32_t headerIdentifier) {
  // Required Data
  boot_svc_msg_t boot_svc_msg{};
  boot_data_t boot_data{};
  boot_log_t boot_log{};
  lifecycle_state_t lc_state{};
  owner_application_keyring_t keyring{};
  size_t verify_key;
  owner_config_t owner_config{};
  uint32_t isfb_check_count;

  // Header Configuration
  boot_svc_msg.header.identifier = headerIdentifier;

  rom_error_t error =
      boot_svc_handler(&boot_svc_msg, &boot_data, &boot_log, lc_state, &keyring,
                       &verify_key, &owner_config, &isfb_check_count);

  switch (headerIdentifier) {
    case kBootSvcIdentifier:
      EXPECT_NE(error, kErrorOk);
      break;
    default:
      EXPECT_EQ(error, kErrorOk);
  }

  EXPECT_EQ(boot_svc_msg.header.identifier, headerIdentifier);
}

/**
 * The `header` message has the following fields:
 * - `hmac_digest_t digest`
 * - `uint32_t identifier`
 * - `uint32_t type`
 * - `uint32_t length`
 *
 * All `type` values except the following should
 * be ignored and return `kErrorOk`:
 * - `kBootSvcEnterRescueReqType`
 * - `kBootSvcNextBl0SlotReqType`
 * - `kBootSvcMinBl0SecVerReqType`
 * - `kBootSvcOwnershipUnlockReqType`
 * - `kBootSvcOwnershipActivateReqType`
 */
void HeaderType(uint32_t headerType) {
  // Required Data
  boot_svc_msg_t boot_svc_msg{};
  boot_data_t boot_data{};
  boot_log_t boot_log{};
  lifecycle_state_t lc_state{};
  owner_application_keyring_t keyring{};
  size_t verify_key;
  owner_config_t owner_config{};
  uint32_t isfb_check_count;

  // Required Mocks
  rom_test::NiceMockHmac mock_hmac_;

  // Header Configuration
  boot_svc_msg.header.identifier = kBootSvcIdentifier;
  boot_svc_msg.header.type = headerType;

  boot_svc_msg.header.length = CHIP_BOOT_SVC_MSG_HEADER_SIZE;
  boot_svc_msg.header.digest = hmac_digest_t{0x1234};

  ON_CALL(mock_hmac_, sha256)
      .WillByDefault(SetArgPointee<2>(hmac_digest_t{0x1234}));

  rom_error_t error =
      boot_svc_handler(&boot_svc_msg, &boot_data, &boot_log, lc_state, &keyring,
                       &verify_key, &owner_config, &isfb_check_count);

  switch (headerType) {
    case kBootSvcEnterRescueReqType:
    case kBootSvcNextBl0SlotReqType:
    case kBootSvcMinBl0SecVerReqType:
    case kBootSvcOwnershipUnlockReqType:
    case kBootSvcOwnershipActivateReqType:
      EXPECT_NE(error, kErrorOk);
      break;
    default:
      EXPECT_EQ(error, kErrorOk);
  }

  EXPECT_EQ(boot_svc_msg.header.type, headerType);
}

/**
 * The `header` message has the following fields:
 * - `hmac_digest_t digest`
 * - `uint32_t identifier`
 * - `uint32_t type`
 * - `uint32_t length`
 *
 * Only valid `length` and `digest` values should
 * be accepted and return `kErrorOk`.
 */
void HeaderLengthAndDigest(uint32_t headerLength, uint32_t hashDigest) {
  // Required Data
  boot_svc_msg_t boot_svc_msg{};
  boot_data_t boot_data{};
  boot_log_t boot_log{};
  lifecycle_state_t lc_state{};
  owner_application_keyring_t keyring{};
  size_t verify_key;
  owner_config_t owner_config{};
  uint32_t isfb_check_count;

  // Required Mocks
  rom_test::NiceMockHmac mock_hmac_;

  // Header Configuration
  boot_svc_msg.header.identifier = kBootSvcIdentifier;
  boot_svc_msg.header.length = headerLength;
  boot_svc_msg.header.digest = hmac_digest_t{hashDigest};

  ON_CALL(mock_hmac_, sha256)
      .WillByDefault(SetArgPointee<2>(hmac_digest_t{hashDigest}));

  rom_error_t error =
      boot_svc_handler(&boot_svc_msg, &boot_data, &boot_log, lc_state, &keyring,
                       &verify_key, &owner_config, &isfb_check_count);

  if (headerLength >= CHIP_BOOT_SVC_MSG_HEADER_SIZE &&
      headerLength <= CHIP_BOOT_SVC_MSG_SIZE_MAX) {
    EXPECT_EQ(error, kErrorOk);
  } else {
    EXPECT_NE(error, kErrorOk);
  }

  EXPECT_EQ(boot_svc_msg.header.length, headerLength);
}

/**
 * The `empty` message has the following fields:
 * - `boot_svc_header_t header`
 * - `uint32_t payload[kBootSvcEmptyPayloadWordCount]`
 *
 * The payload should remain unchanged between the request
 * and response messages.
 */
void EmptyReq(uint32_t payloadValue) {
  // Required Data
  boot_svc_msg_t boot_svc_msg{};
  boot_data_t boot_data{};
  boot_log_t boot_log{};
  lifecycle_state_t lc_state{};
  owner_application_keyring_t keyring{};
  size_t verify_key;
  owner_config_t owner_config{};
  uint32_t isfb_check_count;

  // Required Mocks
  rom_test::NiceMockHmac mock_hmac_;

  // Header Configuration
  boot_svc_msg.header.identifier = kBootSvcIdentifier;
  boot_svc_msg.header.type = kBootSvcEmptyReqType;
  boot_svc_msg.header.length = sizeof(boot_svc_empty_t);
  boot_svc_msg.header.digest = hmac_digest_t{0x1234};

  // Message Configuration
  uint32_t i = 0, j = kBootSvcEmptyPayloadWordCount - 1;
  for (; launder32(i) < kBootSvcEmptyPayloadWordCount &&
         launder32(j) < kBootSvcEmptyPayloadWordCount;
       ++i, --j) {
    boot_svc_msg.empty.payload[i] = payloadValue;
  }

  ON_CALL(mock_hmac_, sha256)
      .WillByDefault(SetArgPointee<2>(hmac_digest_t{0x1234}));

  rom_error_t error =
      boot_svc_handler(&boot_svc_msg, &boot_data, &boot_log, lc_state, &keyring,
                       &verify_key, &owner_config, &isfb_check_count);

  EXPECT_EQ(error, kErrorOk);

  EXPECT_THAT(boot_svc_msg.empty.payload, Each(payloadValue));
}

/**
 * The `enter_rescue_req` message has the following fields:
 * - `boot_svc_header_t header`
 * - `uint32_t skip_once`
 *
 * The value of `skip_once` does not affect the `enter_rescue_res`
 * message in any way, as it only modifies global state.
 *
 * TODO(cmacd): Add way to validate `skip_once` affect, either via
 * public function or via new field in response message.
 */
void EnterRescueReq(uint32_t skipOnce) {
  // Required Data
  boot_svc_msg_t boot_svc_msg{};
  boot_data_t boot_data{};
  boot_log_t boot_log{};
  lifecycle_state_t lc_state{};
  owner_application_keyring_t keyring{};
  size_t verify_key;
  owner_config_t owner_config{};
  uint32_t isfb_check_count;

  // Required Mocks
  rom_test::NiceMockHmac mock_hmac_;

  // Header Configuration
  boot_svc_msg.header.identifier = kBootSvcIdentifier;
  boot_svc_msg.header.type = kBootSvcEnterRescueReqType;
  boot_svc_msg.header.length = sizeof(boot_svc_enter_rescue_req_t);
  boot_svc_msg.header.digest = hmac_digest_t{0x1234};

  // Message Configuration
  boot_svc_msg.enter_rescue_req.skip_once = skipOnce;

  ON_CALL(mock_hmac_, sha256)
      .WillByDefault(SetArgPointee<2>(hmac_digest_t{0x1234}));

  rom_error_t error =
      boot_svc_handler(&boot_svc_msg, &boot_data, &boot_log, lc_state, &keyring,
                       &verify_key, &owner_config, &isfb_check_count);

  EXPECT_EQ(error, kErrorOk);

  EXPECT_EQ(boot_svc_msg.enter_rescue_res.status, kErrorOk);
}

/**
 * The `min_bl0_sec_ver_req` message has the following fields:
 * - `boot_svc_header_t header`
 * - `uint32_t min_bl0_sec_ver`
 *
 * If the requested next security version is at least 1 higher than the
 * current security version and less than or equal to the minimum
 * security version across Slot A and Slot B, it is valid and should return
 * `kErrorOk`.
 */
void SetMinimumSecurityVersionReq(uint32_t nextVersion, uint32_t slotAVersion,
                                  uint32_t slotBVersion,
                                  uint32_t bootDataCurrentVersion) {
  // We can't increase the min security version, if it is already maxed.
  if (slotAVersion == UINT32_MAX || slotBVersion == UINT32_MAX ||
      bootDataCurrentVersion == UINT32_MAX) {
    return;
  }

  uint32_t max_expected_version =
      slotAVersion > slotBVersion ? slotBVersion : slotAVersion;

  // We assume that the current security version is valid.
  if (max_expected_version < bootDataCurrentVersion) {
    return;
  }

  // Required Data
  boot_svc_msg_t boot_svc_msg{};
  boot_data_t boot_data{};
  boot_log_t boot_log{};
  lifecycle_state_t lc_state{};
  owner_application_keyring_t keyring{};
  size_t verify_key;
  owner_config_t owner_config{};
  uint32_t isfb_check_count;

  // Required Mocks
  rom_test::NiceMockHmac mock_hmac_;
  rom_test::NiceMockRomExtBootPolicyPtrs mock_rom_ext_boot_policy_ptrs_;
  rom_test::NiceMockManifest mock_manifest_;
  rom_test::NiceMockBootData mock_boot_data_;
  rom_test::NiceMockLifecycle mock_lifecycle_;
  rom_test::NiceMockOwnerVerify mock_owner_verify_;
  rom_test::NiceMockRnd mock_rnd_;
  rom_test::NiceMockOtp mock_otp_;

  // Header Configuration
  boot_svc_msg.header.identifier = kBootSvcIdentifier;
  boot_svc_msg.header.type = kBootSvcMinBl0SecVerReqType;
  boot_svc_msg.header.length = sizeof(boot_svc_min_bl0_sec_ver_req_t);
  boot_svc_msg.header.digest = hmac_digest_t{0x1234};

  // Message Configuration
  boot_svc_msg.min_bl0_sec_ver_req.min_bl0_sec_ver = nextVersion;

  // Boot Data Configuration
  boot_data.min_security_version_bl0 = bootDataCurrentVersion;

  // Owner Configuration
  owner_config.isfb = (owner_isfb_config_t *)kHardenedBoolFalse;

  owner_application_key_t key = {
      .header =
          {
              .tag = kTlvTagApplicationKey,
              .length = sizeof(owner_application_key_t),
          },
      .key_alg = kOwnershipKeyAlgEcdsaP256,
  };

  // Keyring Configuration
  keyring.length = 1;
  keyring.key[0] = &key;

  // Manifest Configuration
  manifest_ext_spx_key_t spx_key = {.key{.data = {0}}};

  manifest_t manifest_a{};
  manifest_t manifest_b{};

  manifest_a.identifier = CHIP_BL0_IDENTIFIER;
  manifest_a.length = CHIP_BL0_SIZE_MIN;
  manifest_a.security_version = slotAVersion;
  manifest_a.manifest_version.major = kManifestVersionMajor2;
  manifest_a.length = sizeof(manifest_t) + 0x1000;
  manifest_a.signed_region_end = sizeof(manifest_t) + 0x900;
  manifest_a.code_start = sizeof(manifest_t);
  manifest_a.code_end = sizeof(manifest_t) + 0x800;
  manifest_a.entry_point = 0x500;
  manifest_a.ecdsa_public_key.x[0] = 0;

  manifest_b.identifier = CHIP_BL0_IDENTIFIER;
  manifest_b.length = CHIP_BL0_SIZE_MIN;
  manifest_b.security_version = slotBVersion;
  manifest_b.manifest_version.major = kManifestVersionMajor2;
  manifest_b.length = sizeof(manifest_t) + 0x1000;
  manifest_b.signed_region_end = sizeof(manifest_t) + 0x900;
  manifest_b.code_start = sizeof(manifest_t);
  manifest_b.code_end = sizeof(manifest_t) + 0x800;
  manifest_b.entry_point = 0x500;
  manifest_b.ecdsa_public_key.x[0] = 0;

  ON_CALL(mock_hmac_, sha256)
      .WillByDefault(SetArgPointee<2>(hmac_digest_t{0x1234}));

  ON_CALL(mock_rom_ext_boot_policy_ptrs_, ManifestA)
      .WillByDefault(Return(&manifest_a));

  ON_CALL(mock_rom_ext_boot_policy_ptrs_, ManifestB)
      .WillByDefault(Return(&manifest_b));

  ON_CALL(mock_manifest_, SpxKey)
      .WillByDefault(DoAll(SetArgPointee<1>(&spx_key), Return(kErrorOk)));

  ON_CALL(mock_manifest_, SpxSignature).WillByDefault(Return(kErrorOk));

  ON_CALL(mock_owner_verify_, verify).WillByDefault(Return(kErrorOk));

  ON_CALL(mock_boot_data_, Write).WillByDefault(Return(kErrorOk));
  ON_CALL(mock_boot_data_, Read).WillByDefault(Return(kErrorOk));

  rom_error_t error =
      boot_svc_handler(&boot_svc_msg, &boot_data, &boot_log, lc_state, &keyring,
                       &verify_key, &owner_config, &isfb_check_count);

  EXPECT_EQ(error, kErrorOk);

  if (nextVersion > bootDataCurrentVersion &&
      nextVersion <= max_expected_version) {
    EXPECT_EQ(boot_svc_msg.min_bl0_sec_ver_res.status, kErrorOk);
    EXPECT_EQ(boot_svc_msg.min_bl0_sec_ver_res.min_bl0_sec_ver, nextVersion);
  } else {
    EXPECT_EQ(boot_svc_msg.min_bl0_sec_ver_res.status, kErrorBootSvcBadSecVer);
  }
}

/**
 * The `next_boot_bl0_slot_req` message has the following fields:
 * - `boot_svc_header_t header`
 * - `uint32_t next_bl0_slot`
 * - `uint32_t primary_bl0_slot`
 *
 * Update the primary boot slot and the next boot slot to new values.
 *
 * TODO(cmacd): Add way to validate `new_next_boot_slot` affect, either via
 * public function or via new field in response message.
 */
void SetNextBootSlotReq(uint32_t newPrimaryBootSlot, uint32_t newNextBootSlot,
                        uint32_t bootDataCurrentBootSlot) {
  // Required Data
  boot_svc_msg_t boot_svc_msg{};
  boot_data_t boot_data{};
  boot_log_t boot_log{};
  lifecycle_state_t lc_state{};
  owner_application_keyring_t keyring{};
  size_t verify_key;
  owner_config_t owner_config{};
  uint32_t isfb_check_count;

  // Required Mocks
  rom_test::NiceMockHmac mock_hmac_;
  rom_test::NiceMockBootData mock_boot_data_;

  // Header Configuration
  boot_svc_msg.header.identifier = kBootSvcIdentifier;
  boot_svc_msg.header.type = kBootSvcNextBl0SlotReqType;
  boot_svc_msg.header.length = sizeof(boot_svc_next_boot_bl0_slot_req_t);
  boot_svc_msg.header.digest = hmac_digest_t{0x1234};

  // Message Configuration
  boot_svc_msg.next_boot_bl0_slot_req.primary_bl0_slot = newPrimaryBootSlot;
  boot_svc_msg.next_boot_bl0_slot_req.next_bl0_slot = newNextBootSlot;

  // Boot Data Configuration
  boot_data.primary_bl0_slot = bootDataCurrentBootSlot;

  ON_CALL(mock_hmac_, sha256)
      .WillByDefault(SetArgPointee<2>(hmac_digest_t{0x1234}));

  ON_CALL(mock_boot_data_, Write).WillByDefault(Return(kErrorOk));
  ON_CALL(mock_boot_data_, Read).WillByDefault(Return(kErrorOk));

  rom_error_t error =
      boot_svc_handler(&boot_svc_msg, &boot_data, &boot_log, lc_state, &keyring,
                       &verify_key, &owner_config, &isfb_check_count);

  EXPECT_EQ(error, kErrorOk);

  switch (newPrimaryBootSlot) {
    case kBootSlotA:
    case kBootSlotB:
    case kBootSlotUnspecified:
      break;
    default:
      EXPECT_EQ(boot_svc_msg.next_boot_bl0_slot_res.status,
                kErrorBootSvcBadSlot);
      return;
  }

  switch (newNextBootSlot) {
    case kBootSlotA:
    case kBootSlotB:
    case kBootSlotUnspecified:
      break;
    default:
      EXPECT_EQ(boot_svc_msg.next_boot_bl0_slot_res.status,
                kErrorBootSvcBadSlot);
      return;
  }

  EXPECT_EQ(boot_svc_msg.next_boot_bl0_slot_res.status, kErrorOk);
  EXPECT_EQ(boot_svc_msg.next_boot_bl0_slot_res.primary_bl0_slot,
            newPrimaryBootSlot);
}

/**
 * The `ownership_unlock_req` message has the following fields:
 * - `boot_svc_header_t header`
 * - `uint32_t unlock_mode`
 * - `uint32_t din[2]`
 * - `nonce_t nonce`
 * - `owner_keydata_t next_owner_key`
 * - `owner_signature_t signature`
 *
 * <SOMETHING>
 */
void OwnershipUnlockReqRandomMode(uint32_t unlockMode) {
  // Required Data
  boot_svc_msg_t boot_svc_msg{};
  boot_data_t boot_data{};
  boot_log_t boot_log{};
  lifecycle_state_t lc_state{};
  owner_application_keyring_t keyring{};
  size_t verify_key;
  owner_config_t owner_config{};
  uint32_t isfb_check_count;

  // Required Mocks
  rom_test::NiceMockHmac mock_hmac_;
  rom_test::NiceMockRnd mock_rnd_;
  rom_test::NiceMockLifecycle mock_lifecycle_;
  rom_test::NiceMockOwnershipKey mock_ownership_key_;

  // Header Configuration
  boot_svc_msg.header.identifier = kBootSvcIdentifier;
  boot_svc_msg.header.type = kBootSvcOwnershipUnlockReqType;
  boot_svc_msg.header.length = sizeof(boot_svc_ownership_unlock_req_t);
  boot_svc_msg.header.digest = hmac_digest_t{0x1234};

  // Message Configuration
  boot_svc_msg.ownership_unlock_req.unlock_mode = unlockMode;

  // Boot Data Configuration
  boot_data.ownership_state = kOwnershipStateUnlockedAny;
  boot_data.nonce = {0x55555555, 0xAAAAAAAA};

  ON_CALL(mock_hmac_, sha256)
      .WillByDefault(SetArgPointee<2>(hmac_digest_t{0x1234}));

  ON_CALL(mock_ownership_key_, validate).WillByDefault(Return(kErrorOk));

  ON_CALL(mock_lifecycle_, DeviceId)
      .WillByDefault(SetArgPointee<0>((lifecycle_device_id_t){0}));

  ON_CALL(mock_rnd_, Uint32).WillByDefault(Return(5));

  rom_error_t error =
      boot_svc_handler(&boot_svc_msg, &boot_data, &boot_log, lc_state, &keyring,
                       &verify_key, &owner_config, &isfb_check_count);

  switch (unlockMode) {
    case kBootSvcUnlockAny:
    case kBootSvcUnlockEndorsed:
    case kBootSvcUnlockUpdate:
    case kBootSvcUnlockAbort:
      EXPECT_NE(error, kErrorOwnershipInvalidRequest);
      EXPECT_NE(boot_svc_msg.ownership_unlock_res.status,
                kErrorOwnershipInvalidRequest);
      EXPECT_NE(boot_svc_msg.ownership_unlock_res.status, kErrorOk);
      break;
    default:
      EXPECT_EQ(error, kErrorOwnershipInvalidRequest);
      EXPECT_EQ(boot_svc_msg.ownership_unlock_res.status,
                kErrorOwnershipInvalidRequest);
  }
}

/**
 * The `ownership_unlock_req` message has the following fields:
 * - `boot_svc_header_t header`
 * - `uint32_t unlock_mode`
 * - `uint32_t din[2]`
 * - `nonce_t nonce`
 * - `owner_keydata_t next_owner_key`
 * - `owner_signature_t signature`
 *
 * <SOMETHING>
 */
void OwnershipUnlockReqAbortMode(uint32_t nonceA, uint32_t nonceB,
                                 uint32_t dinA, uint32_t dinB,
                                 uint32_t bootDataOwnershipState) {
  // Required Data
  boot_svc_msg_t boot_svc_msg{};
  boot_data_t boot_data{};
  boot_log_t boot_log{};
  lifecycle_state_t lc_state{};
  lifecycle_device_id_t device_id;
  owner_application_keyring_t keyring{};
  size_t verify_key;
  owner_config_t owner_config{};
  uint32_t isfb_check_count;

  // Required Mocks
  rom_test::NiceMockHmac mock_hmac_;
  rom_test::NiceMockRnd mock_rnd_;
  rom_test::NiceMockLifecycle mock_lifecycle_;
  rom_test::NiceMockOwnershipKey mock_ownership_key_;

  // Header Configuration
  boot_svc_msg.header.identifier = kBootSvcIdentifier;
  boot_svc_msg.header.type = kBootSvcOwnershipUnlockReqType;
  boot_svc_msg.header.length = sizeof(boot_svc_ownership_unlock_req_t);
  boot_svc_msg.header.digest = hmac_digest_t{0x1234};

  // Message Configuration
  boot_svc_msg.ownership_unlock_req.unlock_mode = kBootSvcUnlockAbort;
  boot_svc_msg.ownership_unlock_req.din[0] = dinA;
  boot_svc_msg.ownership_unlock_req.din[1] = dinB;
  boot_svc_msg.ownership_unlock_req.nonce = {nonceA, nonceB};

  // Boot Data Configuration
  boot_data.ownership_state = bootDataOwnershipState;
  boot_data.nonce = {nonceA, nonceB};

  // Device Id Configuration
  device_id.device_id[1] = dinA;
  device_id.device_id[2] = dinB;

  ON_CALL(mock_hmac_, sha256)
      .WillByDefault(SetArgPointee<2>(hmac_digest_t{0x1234}));

  ON_CALL(mock_ownership_key_, validate).WillByDefault(Return(kErrorOk));

  ON_CALL(mock_lifecycle_, DeviceId).WillByDefault(SetArgPointee<0>(device_id));

  ON_CALL(mock_rnd_, Uint32).WillByDefault(Return(5));

  rom_error_t error =
      boot_svc_handler(&boot_svc_msg, &boot_data, &boot_log, lc_state, &keyring,
                       &verify_key, &owner_config, &isfb_check_count);

  switch (bootDataOwnershipState) {
    case kOwnershipStateUnlockedEndorsed:
    case kOwnershipStateUnlockedAny:
    case kOwnershipStateUnlockedSelf:
    case kBootSvcUnlockAbort:
      EXPECT_EQ(error, kErrorWriteBootdataThenReboot);
      EXPECT_EQ(boot_svc_msg.ownership_unlock_res.status, kErrorOk);
      break;
    default:
      EXPECT_EQ(error, kErrorOwnershipInvalidState);
      EXPECT_EQ(boot_svc_msg.ownership_unlock_res.status,
                kErrorOwnershipInvalidState);
  }
}

/**
 * The `ownership_unlock_req` message has the following fields:
 * - `boot_svc_header_t header`
 * - `uint32_t unlock_mode`
 * - `uint32_t din[2]`
 * - `nonce_t nonce`
 * - `owner_keydata_t next_owner_key`
 * - `owner_signature_t signature`
 *
 * <SOMETHING>
 */
void OwnershipUnlockReqUpdateMode(uint32_t nonceA, uint32_t nonceB,
                                  uint32_t dinA, uint32_t dinB,
                                  uint32_t bootDataOwnershipState,
                                  uint32_t ownerPageUpdateMode) {
  // Required Data
  boot_svc_msg_t boot_svc_msg{};
  boot_data_t boot_data{};
  boot_log_t boot_log{};
  lifecycle_state_t lc_state{};
  lifecycle_device_id_t device_id;
  owner_application_keyring_t keyring{};
  size_t verify_key;
  owner_config_t owner_config{};
  uint32_t isfb_check_count;

  // Required Mocks
  rom_test::NiceMockHmac mock_hmac_;
  rom_test::NiceMockRnd mock_rnd_;
  rom_test::NiceMockLifecycle mock_lifecycle_;
  rom_test::NiceMockOwnershipKey mock_ownership_key_;

  // Header Configuration
  boot_svc_msg.header.identifier = kBootSvcIdentifier;
  boot_svc_msg.header.type = kBootSvcOwnershipUnlockReqType;
  boot_svc_msg.header.length = sizeof(boot_svc_ownership_unlock_req_t);
  boot_svc_msg.header.digest = hmac_digest_t{0x1234};

  // Message Configuration
  boot_svc_msg.ownership_unlock_req.unlock_mode = kBootSvcUnlockUpdate;
  boot_svc_msg.ownership_unlock_req.din[0] = dinA;
  boot_svc_msg.ownership_unlock_req.din[1] = dinB;
  boot_svc_msg.ownership_unlock_req.nonce = {nonceA, nonceB};

  // Boot Data Configuration
  boot_data.ownership_state = bootDataOwnershipState;
  boot_data.nonce = {nonceA, nonceB};

  // Device Id Configuration
  device_id.device_id[1] = dinA;
  device_id.device_id[2] = dinB;

  // GLOBAL: Owner Block Configuration
  owner_page[0].update_mode = ownerPageUpdateMode;

  ON_CALL(mock_hmac_, sha256)
      .WillByDefault(SetArgPointee<2>(hmac_digest_t{0x1234}));

  ON_CALL(mock_ownership_key_, validate).WillByDefault(Return(kErrorOk));

  ON_CALL(mock_lifecycle_, DeviceId).WillByDefault(SetArgPointee<0>(device_id));

  ON_CALL(mock_rnd_, Uint32).WillByDefault(Return(5));

  rom_error_t error =
      boot_svc_handler(&boot_svc_msg, &boot_data, &boot_log, lc_state, &keyring,
                       &verify_key, &owner_config, &isfb_check_count);

  if (bootDataOwnershipState != kOwnershipStateLockedOwner) {
    EXPECT_EQ(error, kErrorOwnershipInvalidState);
    EXPECT_EQ(boot_svc_msg.ownership_unlock_res.status,
              kErrorOwnershipInvalidState);
    return;
  }

  if (ownerPageUpdateMode == kOwnershipUpdateModeNewVersion) {
    EXPECT_EQ(error, kErrorOwnershipUnlockDenied);
    EXPECT_EQ(boot_svc_msg.ownership_unlock_res.status,
              kErrorOwnershipUnlockDenied);
    return;
  }

  EXPECT_EQ(error, kErrorWriteBootdataThenReboot);
  EXPECT_EQ(boot_svc_msg.ownership_unlock_res.status, kErrorOk);
}

FUZZ_TEST(BootServicesFuzzTest, HeaderIdentifier);
FUZZ_TEST(BootServicesFuzzTest, HeaderType);
FUZZ_TEST(BootServicesFuzzTest, HeaderLengthAndDigest);
FUZZ_TEST(BootServicesFuzzTest, EmptyReq);
FUZZ_TEST(BootServicesFuzzTest, EnterRescueReq);
FUZZ_TEST(BootServicesFuzzTest, SetMinimumSecurityVersionReq);
FUZZ_TEST(BootServicesFuzzTest, SetNextBootSlotReq)
    .WithDomains(ElementOf({kBootSlotA, kBootSlotB}), Arbitrary<uint32_t>(),
                 Arbitrary<uint32_t>());
FUZZ_TEST(BootServicesFuzzTest, OwnershipUnlockReqRandomMode)
    .WithDomains(Arbitrary<uint32_t>().WithSeeds({kBootSvcUnlockAny,
                                                  kBootSvcUnlockEndorsed,
                                                  kBootSvcUnlockUpdate,
                                                  kBootSvcUnlockAbort}));
FUZZ_TEST(BootServicesFuzzTest, OwnershipUnlockReqAbortMode)
    .WithDomains(Arbitrary<uint32_t>(), Arbitrary<uint32_t>(),
                 Arbitrary<uint32_t>(), Arbitrary<uint32_t>(),
                 Arbitrary<uint32_t>().WithSeeds(
                     {kOwnershipStateLockedOwner, kOwnershipStateUnlockedSelf,
                      kOwnershipStateUnlockedAny,
                      kOwnershipStateUnlockedEndorsed,
                      kOwnershipStateRecovery}));

FUZZ_TEST(BootServicesFuzzTest, OwnershipUnlockReqUpdateMode)
    .WithDomains(Arbitrary<uint32_t>(), Arbitrary<uint32_t>(),
                 Arbitrary<uint32_t>(), Arbitrary<uint32_t>(),
                 Arbitrary<uint32_t>().WithSeeds({kOwnershipStateLockedOwner}),
                 Arbitrary<uint32_t>().WithSeeds(
                     {kOwnershipUpdateModeNewVersion,
                      kErrorOwnershipUnlockDenied, kOwnershipUpdateModeSelf,
                      kOwnershipUpdateModeSelfVersion,
                      kOwnershipUpdateModeOpen}));
FUZZ_TEST(BootServicesFuzzTest, HandlerNeverCrashesHeader);
FUZZ_TEST(BootServicesFuzzTest, HandlerNeverCrashesMessages)
    .WithDomains(ElementOf({
                     0x54504d45, /* kBootSvcEmptyReqType */
                     0x51535245, /* kBootSvcEnterRescueReqType */
                     0x5458454e, /* kBootSvcNextBl0SlotReqType */
                     0x4345534d, /* kBootSvcMinBl0SecVerReqType */
                     0x4b4c4e55, /* kBootSvcOwnershipUnlockReqType */
                     0x56544341, /* kBootSvcOwnershipActivateReqType */
                 }),
                 ArrayOf<kBootSvcEmptyPayloadWordCount>(Arbitrary<uint32_t>()));
}  // namespace
}  // namespace boot_services_fuzzest
