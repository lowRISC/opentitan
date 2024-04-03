// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/ownership/ownership_unlock.h"

#include <stdint.h>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "sw/device/lib/base/global_mock.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/boot_svc/mock_boot_svc_header.h"
#include "sw/device/silicon_creator/lib/drivers/mock_hmac.h"
#include "sw/device/silicon_creator/lib/drivers/mock_rnd.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/ownership/datatypes.h"
#include "sw/device/silicon_creator/lib/ownership/mock_ownership_key.h"
#include "sw/device/silicon_creator/lib/ownership/ownership.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace {
using ::testing::_;
using ::testing::Return;

/*
 * The OwnershipUnlockTest fixture provides a pre-initialized bootdata and
 * boot_svc_msg with relevant values filled in.  The tests will have to
 * modify some of these values (ie: ownership_state or the unlock request
 * type) to test the various code-paths in the ownership unlock module.
 */
class OwnershipUnlockTest : public rom_test::RomTest {
 protected:
  boot_data_t bootdata_ = {
      .nonce = {1, 2},
      .ownership_state = kOwnershipStateLockedOwner,
  };
  boot_svc_msg_t message_ = {
      .ownership_unlock_req =
          {
              .header =
                  {
                      .type = kBootSvcOwnershipUnlockReqType,
                  },
              .nonce = {1, 2},
          },
  };

  rom_test::MockHmac hmac_;
  rom_test::MockRnd rnd_;
  rom_test::MockBootSvcHeader hdr_;
  rom_test::MockOwnershipKey ownership_key_;
};

class OwnershipUnlockAnyStateTest
    : public OwnershipUnlockTest,
      public testing::WithParamInterface<ownership_state_t> {};

class OwnershipUnlockEndorsedStateTest
    : public OwnershipUnlockTest,
      public testing::WithParamInterface<ownership_state_t> {};

class OwnershipUnlockedUpdateStateTest
    : public OwnershipUnlockTest,
      public testing::WithParamInterface<ownership_state_t> {};

class OwnershipUnlockAbortValidStateTest
    : public OwnershipUnlockTest,
      public testing::WithParamInterface<ownership_state_t> {};

class OwnershipUnlockAbortInvalidStateTest
    : public OwnershipUnlockTest,
      public testing::WithParamInterface<ownership_state_t> {};

// Tests that a bad `unlock_mode` returns an Invalid Request.
TEST_F(OwnershipUnlockTest, BadUnlockMode) {
  message_.ownership_unlock_req.unlock_mode = 12345;
  EXPECT_CALL(hdr_, Finalize(_, _, _));
  rom_error_t error = ownership_unlock_handler(&message_, &bootdata_);
  EXPECT_EQ(error, kErrorOwnershipInvalidRequest);
}

// Test that requesting LockedOwner->UnlockedAny works.
TEST_F(OwnershipUnlockTest, UnlockAny) {
  message_.ownership_unlock_req.unlock_mode = kBootSvcUnlockAny;
  EXPECT_CALL(ownership_key_,
              validate(0,
                       static_cast<ownership_key_t>(kOwnershipKeyUnlock |
                                                    kOwnershipKeyRecovery),
                       _, _, _))
      .WillOnce(Return(kHardenedBoolTrue));
  EXPECT_CALL(rnd_, Uint32()).WillRepeatedly(Return(5));
  EXPECT_CALL(hdr_, Finalize(_, _, _));

  rom_error_t error = ownership_unlock_handler(&message_, &bootdata_);
  EXPECT_EQ(error, kErrorWriteBootdataThenReboot);
  EXPECT_EQ(bootdata_.nonce.value[0], 5);
  EXPECT_EQ(bootdata_.nonce.value[1], 5);
  EXPECT_EQ(bootdata_.ownership_state, kOwnershipStateUnlockedAny);
}

// Test that requesting LockedOwner->UnlockedAny fails when the signature is
// bad.
TEST_F(OwnershipUnlockTest, UnlockAnyBadSignature) {
  message_.ownership_unlock_req.unlock_mode = kBootSvcUnlockAny;
  EXPECT_CALL(ownership_key_,
              validate(0,
                       static_cast<ownership_key_t>(kOwnershipKeyUnlock |
                                                    kOwnershipKeyRecovery),
                       _, _, _))
      .WillOnce(Return(kHardenedBoolFalse));
  EXPECT_CALL(hdr_, Finalize(_, _, _));

  rom_error_t error = ownership_unlock_handler(&message_, &bootdata_);
  EXPECT_EQ(error, kErrorOwnershipInvalidSignature);
  EXPECT_EQ(bootdata_.ownership_state, kOwnershipStateLockedOwner);
}

// Test that requesting LockedOwner->UnlockedAny fails when the nonce doesn't
// match.
TEST_F(OwnershipUnlockTest, UnlockAnyBadNonce) {
  message_.ownership_unlock_req.unlock_mode = kBootSvcUnlockAny;
  message_.ownership_unlock_req.nonce = {3, 4};
  EXPECT_CALL(ownership_key_,
              validate(0,
                       static_cast<ownership_key_t>(kOwnershipKeyUnlock |
                                                    kOwnershipKeyRecovery),
                       _, _, _))
      .WillOnce(Return(kHardenedBoolTrue));
  EXPECT_CALL(hdr_, Finalize(_, _, _));

  rom_error_t error = ownership_unlock_handler(&message_, &bootdata_);
  EXPECT_EQ(error, kErrorOwnershipInvalidNonce);
  EXPECT_EQ(bootdata_.ownership_state, kOwnershipStateLockedOwner);
}

// Test that requesting UnlockedAny all non-LockedOwner states fails.
TEST_P(OwnershipUnlockAnyStateTest, InvalidState) {
  message_.ownership_unlock_req.unlock_mode = kBootSvcUnlockAny;
  bootdata_.ownership_state = static_cast<uint32_t>(GetParam());
  EXPECT_CALL(hdr_, Finalize(_, _, _));

  rom_error_t error = ownership_unlock_handler(&message_, &bootdata_);
  EXPECT_EQ(error, kErrorOwnershipInvalidState);
}

INSTANTIATE_TEST_SUITE_P(AllCases, OwnershipUnlockAnyStateTest,
                         testing::Values(kOwnershipStateLockedUpdate,
                                         kOwnershipStateUnlockedAny,
                                         kOwnershipStateUnlockedEndorsed));

// Test that requesting LockedOwner->UnlockedEndorsed works.
TEST_F(OwnershipUnlockTest, UnlockEndorsed) {
  message_.ownership_unlock_req.unlock_mode = kBootSvcUnlockEndorsed;
  EXPECT_CALL(ownership_key_,
              validate(0,
                       static_cast<ownership_key_t>(kOwnershipKeyUnlock |
                                                    kOwnershipKeyRecovery),
                       _, _, _))
      .WillOnce(Return(kHardenedBoolTrue));
  EXPECT_CALL(hmac_, sha256(_, _, _))
      .WillOnce([&](const void *, size_t, hmac_digest_t *digest) {
        for (size_t i = 0; i < ARRAYSIZE(digest->digest); ++i) {
          digest->digest[i] = i;
        }
      });
  EXPECT_CALL(rnd_, Uint32()).WillRepeatedly(Return(5));
  EXPECT_CALL(hdr_, Finalize(_, _, _));

  rom_error_t error = ownership_unlock_handler(&message_, &bootdata_);
  EXPECT_EQ(error, kErrorWriteBootdataThenReboot);
  EXPECT_EQ(bootdata_.nonce.value[0], 5);
  EXPECT_EQ(bootdata_.nonce.value[1], 5);
  EXPECT_EQ(bootdata_.ownership_state, kOwnershipStateUnlockedEndorsed);
  for (size_t i = 0; i < ARRAYSIZE(bootdata_.next_owner); ++i) {
    EXPECT_EQ(bootdata_.next_owner[i], i);
  }
}

// Test that requesting LockedOwner->UnlockedEndorsed fails when the signature
// is bad.
TEST_F(OwnershipUnlockTest, UnlockEndorsedBadSignature) {
  message_.ownership_unlock_req.unlock_mode = kBootSvcUnlockEndorsed;
  EXPECT_CALL(ownership_key_,
              validate(0,
                       static_cast<ownership_key_t>(kOwnershipKeyUnlock |
                                                    kOwnershipKeyRecovery),
                       _, _, _))
      .WillOnce(Return(kHardenedBoolFalse));
  EXPECT_CALL(hdr_, Finalize(_, _, _));

  rom_error_t error = ownership_unlock_handler(&message_, &bootdata_);
  EXPECT_EQ(error, kErrorOwnershipInvalidSignature);
  EXPECT_EQ(bootdata_.ownership_state, kOwnershipStateLockedOwner);
}

// Test that requesting LockedOwner->UnlockedEndorsed fails when the nonce
// doesn't match.
TEST_F(OwnershipUnlockTest, UnlockEndorsedBadNonce) {
  message_.ownership_unlock_req.unlock_mode = kBootSvcUnlockEndorsed;
  message_.ownership_unlock_req.nonce = {3, 4};
  EXPECT_CALL(ownership_key_,
              validate(0,
                       static_cast<ownership_key_t>(kOwnershipKeyUnlock |
                                                    kOwnershipKeyRecovery),
                       _, _, _))
      .WillOnce(Return(kHardenedBoolTrue));
  EXPECT_CALL(hdr_, Finalize(_, _, _));

  rom_error_t error = ownership_unlock_handler(&message_, &bootdata_);
  EXPECT_EQ(error, kErrorOwnershipInvalidNonce);
  EXPECT_EQ(bootdata_.ownership_state, kOwnershipStateLockedOwner);
}

// Test that requesting UnlockedEndorsed all non-LockedOwner states fails.
TEST_P(OwnershipUnlockEndorsedStateTest, InvalidState) {
  message_.ownership_unlock_req.unlock_mode = kBootSvcUnlockEndorsed;
  bootdata_.ownership_state = static_cast<uint32_t>(GetParam());
  EXPECT_CALL(hdr_, Finalize(_, _, _));

  rom_error_t error = ownership_unlock_handler(&message_, &bootdata_);
  EXPECT_EQ(error, kErrorOwnershipInvalidState);
}

INSTANTIATE_TEST_SUITE_P(AllCases, OwnershipUnlockEndorsedStateTest,
                         testing::Values(kOwnershipStateLockedUpdate,
                                         kOwnershipStateUnlockedAny,
                                         kOwnershipStateUnlockedEndorsed));

// Test that requesting LockedOwner->LockedUpdate works.
TEST_F(OwnershipUnlockTest, UnlockUpdate) {
  message_.ownership_unlock_req.unlock_mode = kBootSvcUnlockUpdate;
  EXPECT_CALL(
      ownership_key_,
      validate(0, static_cast<ownership_key_t>(kOwnershipKeyUnlock), _, _, _))
      .WillOnce(Return(kHardenedBoolTrue));
  EXPECT_CALL(rnd_, Uint32()).WillRepeatedly(Return(5));
  EXPECT_CALL(hdr_, Finalize(_, _, _));

  rom_error_t error = ownership_unlock_handler(&message_, &bootdata_);
  EXPECT_EQ(error, kErrorWriteBootdataThenReboot);
  EXPECT_EQ(bootdata_.nonce.value[0], 5);
  EXPECT_EQ(bootdata_.nonce.value[1], 5);
  EXPECT_EQ(bootdata_.ownership_state, kOwnershipStateLockedUpdate);
}

// Test that requesting LockedOwner->LockedUpdate fails when the signature is
// bad.
TEST_F(OwnershipUnlockTest, UnlockedUpdateBadSignature) {
  message_.ownership_unlock_req.unlock_mode = kBootSvcUnlockUpdate;
  EXPECT_CALL(
      ownership_key_,
      validate(0, static_cast<ownership_key_t>(kOwnershipKeyUnlock), _, _, _))
      .WillOnce(Return(kHardenedBoolFalse));
  EXPECT_CALL(hdr_, Finalize(_, _, _));

  rom_error_t error = ownership_unlock_handler(&message_, &bootdata_);
  EXPECT_EQ(error, kErrorOwnershipInvalidSignature);
  EXPECT_EQ(bootdata_.ownership_state, kOwnershipStateLockedOwner);
}

// Test that requesting LockedOwner->LockedUpdate fails when the nonce doesn't
// match.
TEST_F(OwnershipUnlockTest, UnlockedUpdateBadNonce) {
  message_.ownership_unlock_req.unlock_mode = kBootSvcUnlockUpdate;
  message_.ownership_unlock_req.nonce = {3, 4};

  EXPECT_CALL(
      ownership_key_,
      validate(0, static_cast<ownership_key_t>(kOwnershipKeyUnlock), _, _, _))
      .WillOnce(Return(kHardenedBoolTrue));
  EXPECT_CALL(hdr_, Finalize(_, _, _));

  rom_error_t error = ownership_unlock_handler(&message_, &bootdata_);
  EXPECT_EQ(error, kErrorOwnershipInvalidNonce);
  EXPECT_EQ(bootdata_.ownership_state, kOwnershipStateLockedOwner);
}

// Test that requesting UnlockUpdate all non-LockedOwner states fails.
TEST_P(OwnershipUnlockedUpdateStateTest, InvalidState) {
  message_.ownership_unlock_req.unlock_mode = kBootSvcUnlockUpdate;
  bootdata_.ownership_state = static_cast<uint32_t>(GetParam());
  EXPECT_CALL(hdr_, Finalize(_, _, _));

  rom_error_t error = ownership_unlock_handler(&message_, &bootdata_);
  EXPECT_EQ(error, kErrorOwnershipInvalidState);
}

INSTANTIATE_TEST_SUITE_P(AllCases, OwnershipUnlockedUpdateStateTest,
                         testing::Values(kOwnershipStateLockedUpdate,
                                         kOwnershipStateUnlockedEndorsed,
                                         kOwnershipStateLockedNone));

// Test that requesting an UnlockAbort from valid states works.
TEST_P(OwnershipUnlockAbortValidStateTest, UnlockAbort) {
  message_.ownership_unlock_req.unlock_mode = kBootSvcUnlockAbort;
  bootdata_.ownership_state = static_cast<uint32_t>(GetParam());
  EXPECT_CALL(
      ownership_key_,
      validate(0, static_cast<ownership_key_t>(kOwnershipKeyUnlock), _, _, _))
      .WillOnce(Return(kHardenedBoolTrue));
  EXPECT_CALL(rnd_, Uint32()).WillRepeatedly(Return(5));
  EXPECT_CALL(hdr_, Finalize(_, _, _));

  rom_error_t error = ownership_unlock_handler(&message_, &bootdata_);
  EXPECT_EQ(error, kErrorWriteBootdataThenReboot);
  EXPECT_EQ(bootdata_.nonce.value[0], 5);
  EXPECT_EQ(bootdata_.nonce.value[1], 5);
  EXPECT_EQ(bootdata_.ownership_state, kOwnershipStateLockedOwner);
}

INSTANTIATE_TEST_SUITE_P(AllCases, OwnershipUnlockAbortValidStateTest,
                         testing::Values(kOwnershipStateLockedUpdate,
                                         kOwnershipStateUnlockedEndorsed,
                                         kOwnershipStateUnlockedAny));

// Test that requesting an UnlockAbort from valid states works.
TEST_P(OwnershipUnlockAbortInvalidStateTest, UnlockAbort) {
  message_.ownership_unlock_req.unlock_mode = kBootSvcUnlockAbort;
  bootdata_.ownership_state = static_cast<uint32_t>(GetParam());
  EXPECT_CALL(hdr_, Finalize(_, _, _));

  rom_error_t error = ownership_unlock_handler(&message_, &bootdata_);
  EXPECT_EQ(error, kErrorOwnershipInvalidState);
}

INSTANTIATE_TEST_SUITE_P(AllCases, OwnershipUnlockAbortInvalidStateTest,
                         testing::Values(kOwnershipStateLockedOwner,
                                         kOwnershipStateLockedNone));
}  // namespace
