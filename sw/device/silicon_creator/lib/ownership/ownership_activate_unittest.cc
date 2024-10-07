// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/ownership/ownership_activate.h"

#include <stdint.h>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "sw/device/lib/base/global_mock.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/boot_svc/mock_boot_svc_header.h"
#include "sw/device/silicon_creator/lib/drivers/mock_flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/mock_hmac.h"
#include "sw/device/silicon_creator/lib/drivers/mock_lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/mock_rnd.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/nonce.h"
#include "sw/device/silicon_creator/lib/ownership/datatypes.h"
#include "sw/device/silicon_creator/lib/ownership/mock_ownership_key.h"
#include "sw/device/silicon_creator/lib/ownership/owner_block.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace {
using ::testing::_;
using ::testing::Return;
using ::testing::SetArgPointee;

constexpr nonce_t kDefaultNonce = {1, 2};

class OwnershipActivateTest : public rom_test::RomTest {
 protected:
  void MakePage1StructValid() {
    owner_page[1].header.tag = kTlvTagOwner;
    owner_page[1].header.length = sizeof(owner_page[1]);
    owner_page[1].header.version = (struct_version_t){0, 0};
    owner_page[1].config_version = 0;
    owner_page[1].min_security_version_bl0 = UINT32_MAX;
    memset(owner_page[1].data, 0x5a, sizeof(owner_page[1].data));
  }

  void MakePage1Valid(bool valid) {
    MakePage1StructValid();
    ownership_state_t state =
        static_cast<ownership_state_t>(bootdata_.ownership_state);
    owner_page_valid[1] = kOwnerPageStatusSigned;
    uint32_t modifier = valid ? 0 : 1;

    switch (state) {
      case kOwnershipStateUnlockedEndorsed:
        // In UnlockedEndorsed, the hash of the owner key in page1 must be equal
        // to the value stored in boot_data.
        EXPECT_CALL(hmac_, sha256(_, _, _))
            .WillOnce(SetArgPointee<2>((hmac_digest_t){{
                bootdata_.next_owner[0] + modifier,
                bootdata_.next_owner[1],
                bootdata_.next_owner[2],
                bootdata_.next_owner[3],
                bootdata_.next_owner[4],
                bootdata_.next_owner[5],
                bootdata_.next_owner[6],
                bootdata_.next_owner[7],
            }}));
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

  boot_data_t bootdata_ = {
      .nonce = kDefaultNonce,
      .ownership_state = kOwnershipStateLockedOwner,
  };
  boot_svc_msg_t message_ = {
      .ownership_activate_req =
          {
              .header =
                  {
                      .type = kBootSvcOwnershipActivateReqType,
                  },
              .nonce = kDefaultNonce,
          },
  };

  rom_test::MockHmac hmac_;
  rom_test::MockRnd rnd_;
  rom_test::MockFlashCtrl flash_ctrl_;
  rom_test::MockBootSvcHeader hdr_;
  rom_test::MockLifecycle lifecycle_;
  rom_test::MockOwnershipKey ownership_key_;
};

class OwnershipActivateInvalidStateTest
    : public OwnershipActivateTest,
      public testing::WithParamInterface<ownership_state_t> {};

class OwnershipActivateValidStateTest
    : public OwnershipActivateTest,
      public testing::WithParamInterface<ownership_state_t> {};

// Tests that requesting Activate in all Locked non-Update states fails.
TEST_P(OwnershipActivateInvalidStateTest, InvalidState) {
  bootdata_.ownership_state = static_cast<uint32_t>(GetParam());
  EXPECT_CALL(hdr_, Finalize(_, _, _));

  rom_error_t error = ownership_activate_handler(&message_, &bootdata_);
  EXPECT_EQ(error, kErrorOwnershipInvalidState);
}

INSTANTIATE_TEST_SUITE_P(AllCases, OwnershipActivateInvalidStateTest,
                         testing::Values(kOwnershipStateLockedOwner,
                                         kOwnershipStateRecovery));

// Tests that an owner block with an invalid signature fails.
TEST_P(OwnershipActivateValidStateTest, InvalidVersion) {
  bootdata_.ownership_state = static_cast<uint32_t>(GetParam());
  MakePage1Valid(true);
  owner_page[1].header.version.major = 5;

  EXPECT_CALL(ownership_key_, validate(1, kOwnershipKeyActivate, _, _, _))
      .WillOnce(Return(kHardenedBoolTrue));
  EXPECT_CALL(lifecycle_, DeviceId(_))
      .WillOnce(SetArgPointee<0>((lifecycle_device_id_t){0}));
  EXPECT_CALL(hdr_, Finalize(_, _, _));

  rom_error_t error = ownership_activate_handler(&message_, &bootdata_);
  EXPECT_EQ(error, kErrorOwnershipOWNRVersion);
}

// Tests that an owner block with an invalid signature fails.
TEST_P(OwnershipActivateValidStateTest, InvalidSignature) {
  bootdata_.ownership_state = static_cast<uint32_t>(GetParam());
  // We want to pass the page 1 validity test to check the signature on the
  // message.
  MakePage1Valid(true);
  EXPECT_CALL(ownership_key_, validate(1, kOwnershipKeyActivate, _, _, _))
      .WillOnce(Return(kHardenedBoolFalse));
  EXPECT_CALL(hdr_, Finalize(_, _, _));

  rom_error_t error = ownership_activate_handler(&message_, &bootdata_);
  EXPECT_EQ(error, kErrorOwnershipInvalidSignature);
}

// Tests that an owner block with an invalid nonce fails.
TEST_P(OwnershipActivateValidStateTest, InvalidNonce) {
  bootdata_.ownership_state = static_cast<uint32_t>(GetParam());
  bootdata_.nonce = {3, 4};
  // We want to pass the page 1 validity test to check the nonce of the
  // message.
  MakePage1Valid(true);
  EXPECT_CALL(ownership_key_, validate(1, kOwnershipKeyActivate, _, _, _))
      .WillOnce(Return(kHardenedBoolTrue));
  EXPECT_CALL(hdr_, Finalize(_, _, _));

  rom_error_t error = ownership_activate_handler(&message_, &bootdata_);
  EXPECT_EQ(error, kErrorOwnershipInvalidNonce);
}

// Tests that an owner block with an invalid DIN fails.
TEST_P(OwnershipActivateValidStateTest, InvalidDin) {
  bootdata_.ownership_state = static_cast<uint32_t>(GetParam());
  // We want to pass the page 1 validity test to check the nonce of the
  // message.
  MakePage1Valid(true);
  EXPECT_CALL(ownership_key_, validate(1, kOwnershipKeyActivate, _, _, _))
      .WillOnce(Return(kHardenedBoolTrue));
  EXPECT_CALL(lifecycle_, DeviceId(_))
      .WillOnce(SetArgPointee<0>((lifecycle_device_id_t){0, 1, 1}));
  EXPECT_CALL(hdr_, Finalize(_, _, _));

  rom_error_t error = ownership_activate_handler(&message_, &bootdata_);
  EXPECT_EQ(error, kErrorOwnershipInvalidDin);
}

// Tests that an owner block with an invalid owner page with respect to the
// current update state fails.
TEST_P(OwnershipActivateValidStateTest, OwnerPageInvalid) {
  ownership_state_t state = GetParam();
  if (state == kOwnershipStateUnlockedAny) {
    SUCCEED() << "There are no invalid conditions for UnlockedAny";
    return;
  }
  bootdata_.ownership_state = static_cast<uint32_t>(state);

  rom_error_t expected_result = kErrorOk;
  owner_page[0].owner_key = {{1, 2, 3, 4, 5}};
  bootdata_.next_owner[0] = 12345;
  MakePage1Valid(false);

  switch (state) {
    case kOwnershipStateUnlockedSelf:
    case kOwnershipStateUnlockedEndorsed:
      // Test should fail with "Invalid Info Page".
      expected_result = kErrorOwnershipInvalidInfoPage;
      break;
    default:
      FAIL() << "Invalid state for this test: " << state;
  }

  EXPECT_CALL(hdr_, Finalize(_, _, _));

  rom_error_t error = ownership_activate_handler(&message_, &bootdata_);
  EXPECT_EQ(error, expected_result);
}

// Tests that an owner block with a valid owner page with respect to the current
// unlock state succeeds.
TEST_P(OwnershipActivateValidStateTest, OwnerPageValid) {
  ownership_state_t state = GetParam();
  bootdata_.ownership_state = static_cast<uint32_t>(state);

  owner_page[0].owner_key = {{1}};
  memset(bootdata_.next_owner, 0, sizeof(bootdata_.next_owner));
  bootdata_.next_owner[0] = 12345;
  MakePage1Valid(true);

  EXPECT_CALL(ownership_key_, validate(1, kOwnershipKeyActivate, _, _, _))
      .WillOnce(Return(kHardenedBoolTrue));
  EXPECT_CALL(lifecycle_, DeviceId(_))
      .WillOnce(SetArgPointee<0>((lifecycle_device_id_t){0}));

  switch (state) {
    case kOwnershipStateUnlockedSelf:
    case kOwnershipStateUnlockedAny:
    case kOwnershipStateUnlockedEndorsed:
      // Test should pass.
      break;
    default:
      FAIL() << "Invalid state for this test: " << state;
  }
  // Once the new owner page is determined to be valid, the page will be sealed.
  EXPECT_CALL(ownership_key_, seal_page(1));

  // The sealed page will be written into flash owner slot 1 first.
  EXPECT_CALL(flash_ctrl_,
              InfoErase(&kFlashCtrlInfoPageOwnerSlot1, kFlashCtrlEraseTypePage))
      .WillOnce(Return(kErrorOk));
  EXPECT_CALL(flash_ctrl_, InfoWrite(&kFlashCtrlInfoPageOwnerSlot1, 0,
                                     sizeof(owner_page[1]) / sizeof(uint32_t),
                                     &owner_page[1]))
      .WillOnce(Return(kErrorOk));
  // The sealed page will be written into flash owner slot 0 second.
  EXPECT_CALL(flash_ctrl_,
              InfoErase(&kFlashCtrlInfoPageOwnerSlot0, kFlashCtrlEraseTypePage))
      .WillOnce(Return(kErrorOk));
  EXPECT_CALL(flash_ctrl_, InfoWrite(&kFlashCtrlInfoPageOwnerSlot0, 0,
                                     sizeof(owner_page[1]) / sizeof(uint32_t),
                                     &owner_page[1]))
      .WillOnce(Return(kErrorOk));

  // The nonce will be regenerated.
  EXPECT_CALL(rnd_, Uint32()).WillRepeatedly(Return(99));
  // The boot_svc response will be finalized.
  EXPECT_CALL(hdr_, Finalize(_, _, _));

  rom_error_t error = ownership_activate_handler(&message_, &bootdata_);
  EXPECT_EQ(error, kErrorWriteBootdataThenReboot);
  // After succeeding, the page should be sealed, the nonce changed and the
  // ownership state set to LockedOwner.
  EXPECT_FALSE(nonce_equal(&bootdata_.nonce, &kDefaultNonce));
  EXPECT_EQ(bootdata_.ownership_state, kOwnershipStateLockedOwner);
  // The default value of `owner_page.min_security_version_bl0` should perform
  // no update to the bootdata's minimum version.
  EXPECT_EQ(bootdata_.min_security_version_bl0, 0);
}

// Tests that an owner update with a non-default value of
// `min_security_version_bl0` updates bootdata's copy.
//
// TODO(cfrantz): Refactor this test as it is nearly a complete copy of the
// previous test except for the manipulation of the min_sec_ver.
TEST_P(OwnershipActivateValidStateTest, UpdateBootdataBl0) {
  ownership_state_t state = GetParam();
  bootdata_.ownership_state = static_cast<uint32_t>(state);

  owner_page[0].owner_key = {{1}};
  memset(bootdata_.next_owner, 0, sizeof(bootdata_.next_owner));
  bootdata_.next_owner[0] = 12345;
  MakePage1Valid(true);
  owner_page[1].min_security_version_bl0 = 5;

  EXPECT_CALL(ownership_key_, validate(1, kOwnershipKeyActivate, _, _, _))
      .WillOnce(Return(kHardenedBoolTrue));
  EXPECT_CALL(lifecycle_, DeviceId(_))
      .WillOnce(SetArgPointee<0>((lifecycle_device_id_t){0}));

  switch (state) {
    case kOwnershipStateUnlockedSelf:
    case kOwnershipStateUnlockedAny:
    case kOwnershipStateUnlockedEndorsed:
      // Test should pass.
      break;
    default:
      FAIL() << "Invalid state for this test: " << state;
  }
  // Once the new owner page is determined to be valid, the page will be sealed.
  EXPECT_CALL(ownership_key_, seal_page(1));

  // The sealed page will be written into flash owner slot 1 first.
  EXPECT_CALL(flash_ctrl_,
              InfoErase(&kFlashCtrlInfoPageOwnerSlot1, kFlashCtrlEraseTypePage))
      .WillOnce(Return(kErrorOk));
  EXPECT_CALL(flash_ctrl_, InfoWrite(&kFlashCtrlInfoPageOwnerSlot1, 0,
                                     sizeof(owner_page[1]) / sizeof(uint32_t),
                                     &owner_page[1]))
      .WillOnce(Return(kErrorOk));
  // The sealed page will be written into flash owner slot 0 second.
  EXPECT_CALL(flash_ctrl_,
              InfoErase(&kFlashCtrlInfoPageOwnerSlot0, kFlashCtrlEraseTypePage))
      .WillOnce(Return(kErrorOk));
  EXPECT_CALL(flash_ctrl_, InfoWrite(&kFlashCtrlInfoPageOwnerSlot0, 0,
                                     sizeof(owner_page[1]) / sizeof(uint32_t),
                                     &owner_page[1]))
      .WillOnce(Return(kErrorOk));

  // The nonce will be regenerated.
  EXPECT_CALL(rnd_, Uint32()).WillRepeatedly(Return(99));
  // The boot_svc response will be finalized.
  EXPECT_CALL(hdr_, Finalize(_, _, _));

  rom_error_t error = ownership_activate_handler(&message_, &bootdata_);
  EXPECT_EQ(error, kErrorWriteBootdataThenReboot);
  // After succeeding, the page should be sealed, the nonce changed and the
  // ownership state set to LockedOwner.
  EXPECT_FALSE(nonce_equal(&bootdata_.nonce, &kDefaultNonce));
  EXPECT_EQ(bootdata_.ownership_state, kOwnershipStateLockedOwner);
  // Bootdata should receive the owner_block's minimum version upon activation.
  EXPECT_EQ(bootdata_.min_security_version_bl0, 5);
}

INSTANTIATE_TEST_SUITE_P(AllCases, OwnershipActivateValidStateTest,
                         testing::Values(kOwnershipStateUnlockedSelf,
                                         kOwnershipStateUnlockedAny,
                                         kOwnershipStateUnlockedEndorsed));

}  // namespace
