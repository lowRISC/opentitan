// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom_ext/rom_ext_boot_services.h"

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
#include "sw/device/silicon_creator/lib/sigverify/flash_exec.h"
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

constexpr uint32_t kActivate =
    static_cast<uint32_t>(kBootSvcOwnershipActivateReqType);

constexpr uint32_t kUnlock =
    static_cast<uint32_t>(kBootSvcOwnershipUnlockReqType);

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
  rom_test::MockFlashCtrl mock_flash_ctrl_;
  rom_test::MockOwnerVerify mock_owner_verify_;
  rom_test::MockOwnershipKey mock_ownership_key_;
  rom_test::MockBootSvcHeader boot_svc_header_;

  void MakePage1StructValid() {
    owner_page[1].header.tag = kTlvTagOwner;
    owner_page[1].header.length = sizeof(owner_page[1]);
    owner_page[1].header.version = (struct_version_t){0, 0};
    owner_page[1].config_version = 0;
    owner_page[1].min_security_version_bl0 = UINT32_MAX;
    owner_page[1].lock_constraint = 0;
    memset(owner_page[1].device_id, 0x7e, sizeof(owner_page[1].device_id));
    memset(owner_page[1].data, 0x5a, sizeof(owner_page[1].data));
  }

  void MakePage1Valid(bool valid) {
    MakePage1StructValid();
    ownership_state_t state =
        static_cast<ownership_state_t>(boot_data.ownership_state);
    owner_page_valid[1] = kOwnerPageStatusSigned;
    uint32_t modifier = valid ? 0 : 1;

    switch (state) {
      case kOwnershipStateUnlockedEndorsed:
        // In UnlockedEndorsed, the hash of the owner key in page1 must be equal
        // to the value stored in boot_data.
      case kOwnershipStateUnlockedSelf:

        owner_page[1].owner_key = owner_page[0].owner_key;
        owner_page[1].owner_key.raw[0] += modifier;
        break;
      case kOwnershipStateUnlockedAny:
        // In UnlockedAny, there are no conditions that page1 must meet.
        break;
      case kOwnershipStateLockedOwner:
        owner_page_valid[1] = kOwnerPageStatusSealed;
        break;
      case kOwnershipStateRecovery:
        owner_page_valid[1] = kOwnerPageStatusInvalid;
        break;
    }
  }
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
  boot_svc_msg.header.identifier = kBootSvcIdentifier;
  boot_svc_msg.header.type = kBootSvcEnterRescueReqType;
  boot_svc_msg.header.length = sizeof(boot_svc_enter_rescue_req_t);
  boot_svc_msg.header.digest = hmac_digest_t{0x1234};

  EXPECT_CALL(mock_hmac_, sha256)
      .WillOnce(SetArgPointee<2>(hmac_digest_t{0x1234}));

  EXPECT_CALL(mock_hmac_, sha256)
      .WillOnce(SetArgPointee<2>(hmac_digest_t{0x1234}));

  EXPECT_EQ(
      boot_svc_handler(&boot_svc_msg, &boot_data, &boot_log, lc_state, &keyring,
                       &verify_key, &owner_config, &isfb_check_count),
      kErrorOk);

  EXPECT_EQ(boot_svc_msg.enter_rescue_res.header.identifier,
            kBootSvcIdentifier);
  EXPECT_EQ(boot_svc_msg.enter_rescue_res.header.type,
            kBootSvcEnterRescueResType);

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
  boot_svc_msg.header.identifier = kBootSvcIdentifier;
  boot_svc_msg.header.type = kBootSvcOwnershipUnlockReqType;
  boot_svc_msg.header.digest = hmac_digest_t{0x1234};
  boot_svc_msg.header.length = sizeof(boot_svc_ownership_unlock_req_t);

  boot_svc_msg.ownership_unlock_req.unlock_mode = kBootSvcUnlockAbort;

  boot_data.ownership_state = kOwnershipStateUnlockedAny;
  boot_data.nonce = {0x55555555, 0xAAAAAAAA};
  boot_svc_msg.ownership_unlock_req.nonce = boot_data.nonce;
  boot_svc_msg.ownership_unlock_req.signature = {{100, 101, 102, 103, 104, 105,
                                                  106, 107, 108, 109, 110, 111,
                                                  112, 113, 114, 115}};

  EXPECT_CALL(mock_hmac_, sha256)
      .WillOnce(SetArgPointee<2>(hmac_digest_t{0x1234}));

  EXPECT_CALL(mock_ownership_key_,
              validate(0, static_cast<ownership_key_t>(kOwnershipKeyUnlock),
                       kUnlock, _, _, _, _, _))
      .WillOnce(DoAll(SetArgPointee<7>(kSigverifyFlashExec), Return(kErrorOk)));
  EXPECT_CALL(mock_lifecycle_, DeviceId(_))
      .WillOnce(SetArgPointee<0>((lifecycle_device_id_t){0}));

  EXPECT_CALL(mock_rnd_, Uint32()).WillRepeatedly(Return(5));

  EXPECT_CALL(mock_hmac_, sha256)
      .WillOnce(SetArgPointee<2>(hmac_digest_t{0x1234}));

  EXPECT_EQ(
      boot_svc_handler(&boot_svc_msg, &boot_data, &boot_log, lc_state, &keyring,
                       &verify_key, &owner_config, &isfb_check_count),
      kErrorWriteBootdataThenReboot);

  EXPECT_EQ(boot_svc_msg.ownership_unlock_res.header.identifier,
            kBootSvcIdentifier);
  EXPECT_EQ(boot_svc_msg.ownership_unlock_res.header.type,
            kBootSvcOwnershipUnlockResType);

  EXPECT_EQ(boot_svc_msg.ownership_unlock_res.status, kErrorOk);
}

TEST_F(RomExtBootServicesTest, BootSvcOwnershipActivate) {
  boot_svc_msg.header.identifier = kBootSvcIdentifier;
  boot_svc_msg.header.type = kBootSvcOwnershipActivateReqType;
  boot_svc_msg.header.digest = hmac_digest_t{0x1234};
  boot_svc_msg.header.length = sizeof(boot_svc_ownership_activate_req_t);

  boot_svc_msg.ownership_activate_req.erase_previous = 1;
  boot_svc_msg.ownership_activate_req.primary_bl0_slot = 0;
  boot_svc_msg.ownership_activate_req.nonce = {0x55555555, 0xAAAAAAAA};
  boot_svc_msg.ownership_activate_req.signature = {
      {100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113,
       114, 115}};

  boot_data.ownership_state = kOwnershipStateUnlockedEndorsed;
  boot_data.nonce = {0x55555555, 0xAAAAAAAA};

  owner_page[0].owner_key = {{1}};
  memset(boot_data.next_owner, 0, sizeof(boot_data.next_owner));
  boot_data.next_owner[0] = 0x1234;

  MakePage1Valid(true);

  EXPECT_CALL(mock_hmac_, sha256)
      .WillOnce(SetArgPointee<2>(hmac_digest_t{0x1234}));

  EXPECT_CALL(mock_hmac_, sha256)
      .WillOnce(SetArgPointee<2>(hmac_digest_t{0x1234}));

  EXPECT_CALL(mock_ownership_key_,
              validate(1, kOwnershipKeyActivate, kActivate, _, _, _, _, _))
      .WillOnce(DoAll(SetArgPointee<7>(kSigverifyFlashExec), Return(kErrorOk)));

  EXPECT_CALL(mock_lifecycle_, DeviceId(_))
      .WillOnce(SetArgPointee<0>((lifecycle_device_id_t){0}));

  // Once the new owner page is determined to be valid, the page will be sealed.
  EXPECT_CALL(mock_ownership_key_, seal_page(1));

  // The sealed page will be written into flash owner slot 1 first.
  EXPECT_CALL(mock_flash_ctrl_,
              InfoErase(&kFlashCtrlInfoPageOwnerSlot1, kFlashCtrlEraseTypePage))
      .WillOnce(Return(kErrorOk));

  EXPECT_CALL(
      mock_flash_ctrl_,
      InfoWrite(&kFlashCtrlInfoPageOwnerSlot1, 0,
                sizeof(owner_page[1]) / sizeof(uint32_t), &owner_page[1]))
      .WillOnce(Return(kErrorOk));

  EXPECT_CALL(mock_flash_ctrl_,
              InfoErase(&kFlashCtrlInfoPageOwnerSlot0, kFlashCtrlEraseTypePage))
      .WillOnce(Return(kErrorOk));

  EXPECT_CALL(
      mock_flash_ctrl_,
      InfoWrite(&kFlashCtrlInfoPageOwnerSlot0, 0,
                sizeof(owner_page[1]) / sizeof(uint32_t), &owner_page[1]))
      .WillOnce(Return(kErrorOk));

  if (boot_data.ownership_state != kOwnershipStateUnlockedSelf) {
    EXPECT_CALL(mock_ownership_key_, secret_new(_, _))
        .WillOnce(Return(kErrorOk));
  }

  EXPECT_CALL(mock_rnd_, Uint32()).WillRepeatedly(Return(99));

  EXPECT_CALL(mock_hmac_, sha256)
      .WillOnce(SetArgPointee<2>(hmac_digest_t{0x1234}));

  EXPECT_EQ(
      boot_svc_handler(&boot_svc_msg, &boot_data, &boot_log, lc_state, &keyring,
                       &verify_key, &owner_config, &isfb_check_count),
      kErrorWriteBootdataThenReboot);

  EXPECT_EQ(boot_svc_msg.ownership_activate_res.header.identifier,
            kBootSvcIdentifier);
  EXPECT_EQ(boot_svc_msg.ownership_activate_res.header.type,
            kBootSvcOwnershipActivateResType);

  EXPECT_EQ(boot_svc_msg.ownership_activate_res.status, kErrorOk);
}

}  // namespace
}  // namespace boot_services_unittest
