// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom_ext/rom_ext_boot_services.h"

#include "gtest/gtest.h"
#include "sw/device/silicon_creator/lib/drivers/mock_hmac.h"
#include "sw/device/silicon_creator/lib/drivers/mock_lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/mock_otp.h"
#include "sw/device/silicon_creator/lib/drivers/mock_rnd.h"
#include "sw/device/silicon_creator/lib/mock_boot_data.h"
#include "sw/device/silicon_creator/lib/mock_manifest.h"
#include "sw/device/silicon_creator/lib/ownership/mock_owner_verify.h"
#include "sw/device/silicon_creator/rom_ext/mock_rom_ext_boot_policy_ptrs.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace boot_services_unittest {
namespace {
using ::testing::_;
using ::testing::AnyNumber;
using ::testing::DoAll;
using ::testing::Each;
using ::testing::Return;
using ::testing::SetArgPointee;

class RomExtBootServicesTest : public rom_test::RomTest {
 protected:
  boot_svc_msg_t boot_svc_msg{};
  boot_data_t boot_data{};
  boot_log_t boot_log{};
  lifecycle_state_t lc_state{};
  owner_application_keyring_t keyring{};
  size_t verify_key;
  owner_config_t owner_config{};
  uint32_t isfb_check_count;

  rom_test::MockHmac mock_hmac_;
  rom_test::MockRomExtBootPolicyPtrs rom_ext_boot_policy_ptrs_;
  rom_test::MockManifest mock_manifest_;
  rom_test::MockBootData mock_boot_data_;
  rom_test::MockRnd mock_rnd_;
  rom_test::MockLifecycle mock_lifecycle_;
  rom_test::MockOtp mock_otp_;
  rom_test::MockOwnerVerify mock_owner_verify_;
};

TEST_F(RomExtBootServicesTest, BootSvcDefault) {
  EXPECT_EQ(
      boot_svc_handler(&boot_svc_msg, &boot_data, &boot_log, lc_state, &keyring,
                      &verify_key, &owner_config, &isfb_check_count),
      kErrorOk);

  EXPECT_EQ(boot_svc_msg.header.type, 0);
}

TEST_F(RomExtBootServicesTest, BootSvcEmpty) {
  boot_svc_msg.header.identifier = kBootSvcIdentifier;
  boot_svc_msg.header.type = kBootSvcEmptyReqType;
  boot_svc_msg.header.length = sizeof(boot_svc_empty_t);
  boot_svc_msg.header.digest = hmac_digest_t{0x1234};

  EXPECT_CALL(mock_hmac_, sha256)
      .WillOnce(SetArgPointee<2>(hmac_digest_t{0x1234}));

  EXPECT_CALL(mock_hmac_, sha256)
      .WillOnce(SetArgPointee<2>(hmac_digest_t{0x1234}));

  EXPECT_EQ(
      boot_svc_handler(&boot_svc_msg, &boot_data, &boot_log, lc_state, &keyring,
                      &verify_key, &owner_config, &isfb_check_count),
      kErrorOk);

  EXPECT_EQ(boot_svc_msg.empty.header.identifier, kBootSvcIdentifier);
  EXPECT_EQ(boot_svc_msg.empty.header.type, kBootSvcEmptyResType);

  EXPECT_THAT(boot_svc_msg.empty.payload, Each(0));
}

TEST_F(RomExtBootServicesTest, BootSvcEnterRescue) {
  boot_svc_msg.header.type = kBootSvcEnterRescueReqType;

  EXPECT_EQ(
      boot_svc_handler(&boot_svc_msg, &boot_data, &boot_log, lc_state, &keyring,
                      &verify_key, &owner_config, &isfb_check_count),
      kErrorOk);

  EXPECT_EQ(boot_svc_msg.enter_rescue_res.status, kErrorOk);
}

TEST_F(RomExtBootServicesTest, BootSvcNextBl0Slot) {
  boot_svc_msg.header.identifier = kBootSvcIdentifier;
  boot_svc_msg.header.type = kBootSvcNextBl0SlotReqType;
  boot_svc_msg.header.length = sizeof(boot_svc_next_boot_bl0_slot_req_t);
  boot_svc_msg.header.digest = hmac_digest_t{0x1234};

  boot_svc_msg.next_boot_bl0_slot_req.primary_bl0_slot = kBootSlotA;

  boot_svc_msg.next_boot_bl0_slot_req.next_bl0_slot = kBootSlotB;

  boot_data.primary_bl0_slot = kBootSlotB;

  EXPECT_CALL(mock_hmac_, sha256)
      .WillOnce(SetArgPointee<2>(hmac_digest_t{0x1234}));

  EXPECT_CALL(mock_boot_data_, Write).WillOnce(Return(kErrorOk));

  EXPECT_CALL(mock_boot_data_, Read).WillOnce(Return(kErrorOk));

  EXPECT_CALL(mock_hmac_, sha256)
      .WillOnce(SetArgPointee<2>(hmac_digest_t{0x1234}));

  EXPECT_EQ(
      boot_svc_handler(&boot_svc_msg, &boot_data, &boot_log, lc_state, &keyring,
                      &verify_key, &owner_config, &isfb_check_count),
      kErrorOk);

  EXPECT_EQ(boot_svc_msg.next_boot_bl0_slot_res.header.identifier,
            kBootSvcIdentifier);
  EXPECT_EQ(boot_svc_msg.next_boot_bl0_slot_res.header.type,
            kBootSvcNextBl0SlotResType);

  EXPECT_EQ(boot_svc_msg.next_boot_bl0_slot_res.status, kErrorOk);
}

TEST_F(RomExtBootServicesTest, BootSvcMinBl0SecVer) {
  boot_svc_msg.header.identifier = kBootSvcIdentifier;
  boot_svc_msg.header.type = kBootSvcMinBl0SecVerReqType;
  boot_svc_msg.header.length = sizeof(boot_svc_next_boot_bl0_slot_req_t);
  boot_svc_msg.header.digest = hmac_digest_t{0x1234};

  boot_svc_msg.next_boot_bl0_slot_req.next_bl0_slot = 2;

  boot_data.min_security_version_bl0 = 1;

  owner_config.isfb = (owner_isfb_config_t *)kHardenedBoolFalse;

  owner_application_key_t key = {
      .header =
          {
              .tag = kTlvTagApplicationKey,
              .length = sizeof(owner_application_key_t),
          },
      .key_alg = kOwnershipKeyAlgEcdsaP256,
  };

  keyring.length = 1;
  keyring.key[0] = &key;

  manifest_ext_spx_key_t spx_key = {.key{.data = {0}}};

  manifest_t manifest_a{};
  manifest_t manifest_b{};

  manifest_a.identifier = CHIP_BL0_IDENTIFIER;
  manifest_a.length = CHIP_BL0_SIZE_MIN;
  manifest_a.security_version = 2;
  manifest_a.manifest_version.major = kManifestVersionMajor2;
  manifest_a.length = sizeof(manifest_t) + 0x1000;
  manifest_a.signed_region_end = sizeof(manifest_t) + 0x900;
  manifest_a.code_start = sizeof(manifest_t);
  manifest_a.code_end = sizeof(manifest_t) + 0x800;
  manifest_a.entry_point = 0x500;
  manifest_a.ecdsa_public_key.x[0] = 0;

  manifest_b.identifier = CHIP_BL0_IDENTIFIER;
  manifest_b.length = CHIP_BL0_SIZE_MIN;
  manifest_b.security_version = 3;
  manifest_b.manifest_version.major = kManifestVersionMajor2;
  manifest_b.length = sizeof(manifest_t) + 0x1000;
  manifest_b.signed_region_end = sizeof(manifest_t) + 0x900;
  manifest_b.code_start = sizeof(manifest_t);
  manifest_b.code_end = sizeof(manifest_t) + 0x800;
  manifest_b.entry_point = 0x500;
  manifest_b.ecdsa_public_key.x[0] = 0;

  EXPECT_CALL(mock_hmac_, sha256)
      .WillOnce(SetArgPointee<2>(hmac_digest_t{0x1234}));

  EXPECT_CALL(rom_ext_boot_policy_ptrs_, ManifestA)
      .WillOnce(Return(&manifest_a));
  EXPECT_CALL(mock_manifest_, SpxKey)
      .WillOnce(DoAll(SetArgPointee<1>(&spx_key), Return(kErrorOk)));
  EXPECT_CALL(mock_manifest_, SpxSignature).WillOnce(Return(kErrorOk));

  EXPECT_CALL(mock_rnd_, Uint32);
  EXPECT_CALL(mock_hmac_, sha256_init);
  EXPECT_CALL(mock_lifecycle_, DeviceId);
  EXPECT_CALL(mock_otp_, read32);
  EXPECT_CALL(mock_otp_, read32);
  EXPECT_CALL(mock_lifecycle_, State);
  EXPECT_CALL(mock_hmac_, sha256_update);
  EXPECT_CALL(mock_manifest_, DigestRegion);
  EXPECT_CALL(mock_hmac_, sha256_update);
  EXPECT_CALL(mock_hmac_, sha256_process);
  EXPECT_CALL(mock_hmac_, sha256_final);

  EXPECT_CALL(mock_owner_verify_, verify).WillOnce(Return(kErrorOk));

  EXPECT_CALL(rom_ext_boot_policy_ptrs_, ManifestB)
      .WillOnce(Return(&manifest_b));
  EXPECT_CALL(mock_manifest_, SpxKey)
      .WillOnce(DoAll(SetArgPointee<1>(&spx_key), Return(kErrorOk)));
  EXPECT_CALL(mock_manifest_, SpxSignature).WillOnce(Return(kErrorOk));

  EXPECT_CALL(mock_rnd_, Uint32);
  EXPECT_CALL(mock_hmac_, sha256_init);
  EXPECT_CALL(mock_lifecycle_, DeviceId);
  EXPECT_CALL(mock_otp_, read32);
  EXPECT_CALL(mock_otp_, read32);
  EXPECT_CALL(mock_lifecycle_, State);
  EXPECT_CALL(mock_hmac_, sha256_update);
  EXPECT_CALL(mock_manifest_, DigestRegion);
  EXPECT_CALL(mock_hmac_, sha256_update);
  EXPECT_CALL(mock_hmac_, sha256_process);
  EXPECT_CALL(mock_hmac_, sha256_final);

  EXPECT_CALL(mock_owner_verify_, verify).WillOnce(Return(kErrorOk));

  EXPECT_CALL(mock_boot_data_, Write).WillOnce(Return(kErrorOk));
  EXPECT_CALL(mock_boot_data_, Read).WillOnce(Return(kErrorOk));

  EXPECT_CALL(mock_hmac_, sha256)
      .WillOnce(SetArgPointee<2>(hmac_digest_t{0x1234}));

  EXPECT_EQ(
      boot_svc_handler(&boot_svc_msg, &boot_data, &boot_log, lc_state, &keyring,
                      &verify_key, &owner_config, &isfb_check_count),
      kErrorOk);

  EXPECT_EQ(boot_svc_msg.min_bl0_sec_ver_res.header.identifier,
            kBootSvcIdentifier);
  EXPECT_EQ(boot_svc_msg.min_bl0_sec_ver_res.header.type,
            kBootSvcMinBl0SecVerResType);

  EXPECT_EQ(boot_svc_msg.min_bl0_sec_ver_res.status, kErrorOk);
}

TEST_F(RomExtBootServicesTest, BootSvcOwnershipUnlock) {
  boot_svc_msg.header.type = kBootSvcOwnershipUnlockReqType;

  EXPECT_EQ(
      boot_svc_handler(&boot_svc_msg, &boot_data, &boot_log, lc_state, &keyring,
                      &verify_key, &owner_config, &isfb_check_count),
      kErrorOk);

  EXPECT_EQ(boot_svc_msg.ownership_unlock_res.status, kErrorOk);
}

TEST_F(RomExtBootServicesTest, BootSvcOwnershipActivate) {
  boot_svc_msg.header.type = kBootSvcOwnershipActivateReqType;

  EXPECT_EQ(
      boot_svc_handler(&boot_svc_msg, &boot_data, &boot_log, lc_state, &keyring,
                      &verify_key, &owner_config, &isfb_check_count),
      kErrorOk);

  EXPECT_EQ(boot_svc_msg.ownership_activate_res.status, kErrorOk);
}

}  // namespace
}  // namespace boot_services_unittest
