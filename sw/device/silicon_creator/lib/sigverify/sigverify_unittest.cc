// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/sigverify/sigverify.h"

#include <array>
#include <cstring>
#include <limits>
#include <unordered_set>

#include "gtest/gtest.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/drivers/mock_lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/mock_otp.h"
#include "sw/device/silicon_creator/lib/sigverify/mock_mod_exp_ibex.h"
#include "sw/device/silicon_creator/lib/sigverify/mock_mod_exp_otbn.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

#include "otp_ctrl_regs.h"

namespace sigverify_unittest {
namespace {
using ::testing::DoAll;
using ::testing::NotNull;
using ::testing::Return;
using ::testing::SetArgPointee;

/**
 * SHA2-256 digest of "test".
 *
 * Can be obtained using:
 * ```
 * echo -n "test" | openssl dgst -sha256 -binary | \
 *    xxd -p -c 4 | tac | sed 's|.*|0x&,|'
 * ```
 */
constexpr hmac_digest_t kTestDigest{
    .digest =
        {
            0xb0f00a08,
            0xd15d6c15,
            0x2b0b822c,
            0xa3bf4f1b,
            0xc55ad015,
            0x9a2feaa0,
            0x884c7d65,
            0x9f86d081,
        },
};

/**
 * 3072-bit EMSA-PKCS1-v1_5 encoding of `kTestDigest`.
 *
 * Can be obtained using:
 * ```
 * # Create private key.
 * openssl genrsa -out key.pem 3072
 * # Sign.
 * echo -n "test" | openssl dgst -sha256 -sign key.pem -out signature
 * # Print encoded message.
 * openssl rsautl -verify -in signature -inkey key.pem -raw | \
 *    xxd -p -c 4 | tac | sed 's|.*|0x&,|'
 * ```
 */
constexpr sigverify_rsa_buffer_t kEncMsg{
    .data = {
        0xb0f00a08, 0xd15d6c15, 0x2b0b822c, 0xa3bf4f1b, 0xc55ad015, 0x9a2feaa0,
        0x884c7d65, 0x9f86d081, 0x05000420, 0x03040201, 0x86480165, 0x0d060960,
        0x00303130, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0x0001ffff,
    }};

// The value of `kSignature` is not significant since we use mocks for
// `sigverify_mod_exp_ibex()` and `sigverify_mod_exp_otbn()`.
constexpr sigverify_rsa_buffer_t kSignature{};

/**
 * Life cycle states used in parameterized tests.
 */

constexpr std::array<lifecycle_state_t, 4> kLcStatesNonTestOperational{
    kLcStateDev,
    kLcStateProd,
    kLcStateProdEnd,
    kLcStateRma,
};

class SigverifyInLcState
    : public rom_test::RomTest,
      public testing::WithParamInterface<lifecycle_state_t> {
 protected:
  rom_test::MockSigverifyModExpIbex sigverify_mod_exp_ibex_;
  rom_test::MockSigverifyModExpOtbn sigverify_mod_exp_otbn_;
  rom_test::MockOtp otp_;
  // The content of this key is not significant since we use mocks.
  sigverify_rsa_key_t key_{};
};

class SigverifyInNonTestStates : public SigverifyInLcState {};

TEST_P(SigverifyInNonTestStates, GoodSignatureIbex) {
  EXPECT_CALL(
      otp_,
      read32(
          OTP_CTRL_PARAM_CREATOR_SW_CFG_SIGVERIFY_RSA_MOD_EXP_IBEX_EN_OFFSET))
      .WillOnce(Return(kHardenedBoolTrue));
  EXPECT_CALL(sigverify_mod_exp_ibex_, mod_exp(&key_, &kSignature, NotNull()))
      .WillOnce(DoAll(SetArgPointee<2>(kEncMsg), Return(kErrorOk)));

  uint32_t flash_exec = 0;
  EXPECT_EQ(sigverify_rsa_verify(&kSignature, &key_, &kTestDigest, GetParam(),
                                 &flash_exec),
            kErrorOk);
  EXPECT_EQ(flash_exec, kSigverifyRsaSuccess);
}

TEST_P(SigverifyInNonTestStates, GoodSignatureOtbn) {
  EXPECT_CALL(
      otp_,
      read32(
          OTP_CTRL_PARAM_CREATOR_SW_CFG_SIGVERIFY_RSA_MOD_EXP_IBEX_EN_OFFSET))
      .WillOnce(Return(kHardenedBoolFalse));
  EXPECT_CALL(sigverify_mod_exp_otbn_, mod_exp(&key_, &kSignature, NotNull()))
      .WillOnce(DoAll(SetArgPointee<2>(kEncMsg), Return(kErrorOk)));

  uint32_t flash_exec = 0;
  EXPECT_EQ(sigverify_rsa_verify(&kSignature, &key_, &kTestDigest, GetParam(),
                                 &flash_exec),
            kErrorOk);
  EXPECT_EQ(flash_exec, kSigverifyRsaSuccess);
}

TEST_P(SigverifyInNonTestStates, BadSignatureOtbn) {
  // Corrupt the words of the encoded message by flipping their bits and check
  // that signature verification fails.
  for (size_t i = 0; i < kSigVerifyRsaNumWords; ++i) {
    auto bad_enc_msg = kEncMsg;
    bad_enc_msg.data[i] = ~bad_enc_msg.data[i];

    EXPECT_CALL(
        otp_,
        read32(
            OTP_CTRL_PARAM_CREATOR_SW_CFG_SIGVERIFY_RSA_MOD_EXP_IBEX_EN_OFFSET))
        .WillOnce(Return(kHardenedBoolFalse));
    EXPECT_CALL(sigverify_mod_exp_otbn_, mod_exp(&key_, &kSignature, NotNull()))
        .WillOnce(DoAll(SetArgPointee<2>(bad_enc_msg), Return(kErrorOk)));

    uint32_t flash_exec = 0;
    EXPECT_EQ(sigverify_rsa_verify(&kSignature, &key_, &kTestDigest, GetParam(),
                                   &flash_exec),
              kErrorSigverifyBadRsaSignature);
    EXPECT_EQ(flash_exec, std::numeric_limits<uint32_t>::max());
  }
}

INSTANTIATE_TEST_SUITE_P(NonTestOperationalStates, SigverifyInNonTestStates,
                         testing::ValuesIn(kLcStatesNonTestOperational));

class SigverifyInNonTestStatesDeathTest : public SigverifyInLcState {};

TEST_P(SigverifyInNonTestStatesDeathTest, BadOtpValue) {
  EXPECT_DEATH(
      {
        EXPECT_CALL(
            otp_,
            read32(
                OTP_CTRL_PARAM_CREATOR_SW_CFG_SIGVERIFY_RSA_MOD_EXP_IBEX_EN_OFFSET))
            .WillOnce(Return(0xA5A5A5A5));

        uint32_t flash_exec = 0;
        sigverify_rsa_verify(&kSignature, &key_, &kTestDigest, GetParam(),
                             &flash_exec);
      },
      "");
}

INSTANTIATE_TEST_SUITE_P(NonTestOperationalStatesDeathTest,
                         SigverifyInNonTestStatesDeathTest,
                         testing::ValuesIn(kLcStatesNonTestOperational));

class SigverifyInTestStates : public SigverifyInLcState {};

TEST_F(SigverifyInTestStates, GoodSignatureIbex) {
  EXPECT_CALL(sigverify_mod_exp_ibex_, mod_exp(&key_, &kSignature, NotNull()))
      .WillOnce(DoAll(SetArgPointee<2>(kEncMsg), Return(kErrorOk)));

  uint32_t flash_exec = 0;
  EXPECT_EQ(sigverify_rsa_verify(&kSignature, &key_, &kTestDigest, kLcStateTest,
                                 &flash_exec),
            kErrorOk);
  EXPECT_EQ(flash_exec, kSigverifyRsaSuccess);
}

TEST_F(SigverifyInTestStates, BadSignatureIbex) {
  // Corrupt the words of the encoded message by flipping their bits and check
  // that signature verification fails.
  for (size_t i = 0; i < kSigVerifyRsaNumWords; ++i) {
    auto bad_enc_msg = kEncMsg;
    bad_enc_msg.data[i] = ~bad_enc_msg.data[i];

    EXPECT_CALL(sigverify_mod_exp_ibex_, mod_exp(&key_, &kSignature, NotNull()))
        .WillOnce(DoAll(SetArgPointee<2>(bad_enc_msg), Return(kErrorOk)));

    uint32_t flash_exec = 0;
    EXPECT_EQ(sigverify_rsa_verify(&kSignature, &key_, &kTestDigest,
                                   kLcStateTest, &flash_exec),
              kErrorSigverifyBadRsaSignature);
    EXPECT_EQ(flash_exec, std::numeric_limits<uint32_t>::max());
  }
}

class SigverifyBadLcStateDeathTest : public SigverifyInLcState {};

TEST_F(SigverifyBadLcStateDeathTest, BadLcState) {
  EXPECT_DEATH(
      {
        uint32_t flash_exec = 0;
        sigverify_rsa_verify(&kSignature, &key_, &kTestDigest,
                             static_cast<lifecycle_state_t>(0), &flash_exec);
      },
      "");
}

struct UsageConstraintsTestCase {
  uint32_t selector_bits;
  lifecycle_device_id_t exp_device_id;
  uint32_t exp_manuf_state_creator;
  uint32_t exp_manuf_state_owner;
  uint32_t exp_life_cycle_state;
};

class SigverifyUsageConstraints
    : public rom_test::RomTest,
      public testing::WithParamInterface<UsageConstraintsTestCase> {
 protected:
  rom_test::MockLifecycle lifecycle_;
  rom_test::MockOtp otp_;
};

/**
 * Constants used in usage constraints tests.
 */

constexpr uint32_t kUnusedWord = MANIFEST_USAGE_CONSTRAINT_UNSELECTED_WORD_VAL;
constexpr uint32_t kManufStateCreator = 0x30303030;
constexpr uint32_t kManufStateOwner = 0x31313131;
constexpr uint32_t kLifeCycleState = 0x32323232;
constexpr lifecycle_device_id_t kDeviceId{
    .device_id =
        {
            0x01020304,
            0x05060708,
            0x09100A0B,
            0x0C0D0E0F,
            0x10111213,
            0x14151617,
            0x18192021,
            0x22232425,
        },
};

TEST_F(SigverifyUsageConstraints, ConstantCheck) {
  // Changing this constant breaks compatibility with the ROM, existing
  // images and tools.
  EXPECT_EQ(MANIFEST_USAGE_CONSTRAINT_UNSELECTED_WORD_VAL, 0xA5A5A5A5);
  EXPECT_NE(kManufStateCreator, kUnusedWord);
  EXPECT_NE(kManufStateOwner, kUnusedWord);
  EXPECT_NE(kLifeCycleState, kUnusedWord);
  for (size_t i = 0; i < kLifecycleDeviceIdNumWords; ++i) {
    EXPECT_NE(kDeviceId.device_id[i], kUnusedWord);
  }
}

constexpr std::array<UsageConstraintsTestCase, 4> kUsageConstraintsTestCases{{
    {
        .selector_bits = 0x7FF,
        .exp_device_id = kDeviceId,
        .exp_manuf_state_creator = kManufStateCreator,
        .exp_manuf_state_owner = kManufStateOwner,
        .exp_life_cycle_state = kLifeCycleState,
    },
    {
        .selector_bits = 0x3AA,
        .exp_device_id = {.device_id =
                              {
                                  kUnusedWord,
                                  kDeviceId.device_id[1],
                                  kUnusedWord,
                                  kDeviceId.device_id[3],
                                  kUnusedWord,
                                  kDeviceId.device_id[5],
                                  kUnusedWord,
                                  kDeviceId.device_id[7],
                              }},
        .exp_manuf_state_creator = kUnusedWord,
        .exp_manuf_state_owner = kUnusedWord,
        .exp_life_cycle_state = kUnusedWord,
    },
    {
        .selector_bits = 0x155,
        .exp_device_id = {.device_id =
                              {
                                  kDeviceId.device_id[0],
                                  kUnusedWord,
                                  kDeviceId.device_id[2],
                                  kUnusedWord,
                                  kDeviceId.device_id[4],
                                  kUnusedWord,
                                  kDeviceId.device_id[6],
                                  kUnusedWord,
                              }},
        .exp_manuf_state_creator = kUnusedWord,
        .exp_manuf_state_owner = kUnusedWord,
        .exp_life_cycle_state = kUnusedWord,
    },
    {
        .selector_bits = 0,
        .exp_device_id = {.device_id =
                              {
                                  kUnusedWord,
                                  kUnusedWord,
                                  kUnusedWord,
                                  kUnusedWord,
                                  kUnusedWord,
                                  kUnusedWord,
                                  kUnusedWord,
                                  kUnusedWord,
                              }},
        .exp_manuf_state_creator = kUnusedWord,
        .exp_manuf_state_owner = kUnusedWord,
        .exp_life_cycle_state = kUnusedWord,
    },
}};

TEST_P(SigverifyUsageConstraints, Read) {
  EXPECT_CALL(lifecycle_, DeviceId(NotNull()))
      .WillOnce(SetArgPointee<0>(kDeviceId));

  EXPECT_CALL(otp_, read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_MANUF_STATE_OFFSET))
      .WillOnce(Return(GetParam().exp_manuf_state_creator));

  EXPECT_CALL(otp_, read32(OTP_CTRL_PARAM_OWNER_SW_CFG_MANUF_STATE_OFFSET))
      .WillOnce(Return(GetParam().exp_manuf_state_owner));

  EXPECT_CALL(lifecycle_, State())
      .WillOnce(Return(static_cast<lifecycle_state_t>(kLifeCycleState)));

  manifest_usage_constraints_t usage_constraints;
  sigverify_usage_constraints_get(GetParam().selector_bits, &usage_constraints);

  EXPECT_EQ(usage_constraints.selector_bits, GetParam().selector_bits);
  EXPECT_THAT(usage_constraints.device_id.device_id,
              testing::ElementsAreArray(GetParam().exp_device_id.device_id));
  EXPECT_EQ(usage_constraints.manuf_state_creator,
            GetParam().exp_manuf_state_creator);
  EXPECT_EQ(usage_constraints.manuf_state_owner,
            GetParam().exp_manuf_state_owner);
  EXPECT_EQ(usage_constraints.life_cycle_state,
            GetParam().exp_life_cycle_state);
}

INSTANTIATE_TEST_SUITE_P(UsageConstraintsTestCases, SigverifyUsageConstraints,
                         testing::ValuesIn(kUsageConstraintsTestCases));

TEST(SigverifyRsaSuccessToOk, Result) {
  EXPECT_EQ(sigverify_rsa_success_to_ok(kSigverifyRsaSuccess), kErrorOk);
  EXPECT_NE(sigverify_rsa_success_to_ok(kErrorOk), kErrorOk);
  EXPECT_NE(sigverify_rsa_success_to_ok(std::numeric_limits<uint32_t>::max()),
            kErrorOk);
  EXPECT_NE(sigverify_rsa_success_to_ok(0), kErrorOk);
}

}  // namespace
}  // namespace sigverify_unittest
