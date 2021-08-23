// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/sigverify.h"

#include <cstring>
#include <unordered_set>

#include "gtest/gtest.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/drivers/mock_hmac.h"
#include "sw/device/silicon_creator/lib/drivers/mock_otp.h"
#include "sw/device/silicon_creator/lib/mock_sigverify_mod_exp_ibex.h"
#include "sw/device/silicon_creator/lib/mock_sigverify_mod_exp_otbn.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
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

constexpr std::array<lifecycle_state_t, 8> kLcStatesTest{
    kLcStateTestUnlocked0, kLcStateTestUnlocked1, kLcStateTestUnlocked2,
    kLcStateTestUnlocked3, kLcStateTestUnlocked4, kLcStateTestUnlocked5,
    kLcStateTestUnlocked6, kLcStateTestUnlocked7,
};

constexpr std::array<lifecycle_state_t, 4> kLcStatesNonTestOperational{
    kLcStateDev,
    kLcStateProd,
    kLcStateProdEnd,
    kLcStateRma,
};

constexpr std::array<lifecycle_state_t, 12> kLcStatesNonOperational{
    kLcStateRaw,         kLcStateTestLocked0,
    kLcStateTestLocked1, kLcStateTestLocked2,
    kLcStateTestLocked3, kLcStateTestLocked4,
    kLcStateTestLocked5, kLcStateTestLocked6,
    kLcStateScrap,       kLcStatePostTransition,
    kLcStateEscalate,    kLcStateInvalid,
};

const std::unordered_set<lifecycle_state_t> &LcStatesAll() {
  static const std::unordered_set<lifecycle_state_t> *const kLcStatesAll =
      []() {
        auto states = new std::unordered_set<lifecycle_state_t>();
        states->insert(kLcStatesTest.begin(), kLcStatesTest.end());
        states->insert(kLcStatesNonTestOperational.begin(),
                       kLcStatesNonTestOperational.end());
        states->insert(kLcStatesNonOperational.begin(),
                       kLcStatesNonOperational.end());
        return states;
      }();
  return *kLcStatesAll;
}

TEST(LcStateCount, IsCorrect) {
  EXPECT_EQ(kLcStateNumStates, LcStatesAll().size());
}

class SigverifyInLcState
    : public mask_rom_test::MaskRomTest,
      public testing::WithParamInterface<lifecycle_state_t> {
 protected:
  mask_rom_test::MockSigverifyModExpIbex sigverify_mod_exp_ibex_;
  mask_rom_test::MockSigverifyModExpOtbn sigverify_mod_exp_otbn_;
  mask_rom_test::MockHmac hmac_;
  mask_rom_test::MockOtp otp_;
  // The content of this key is not significant since we use mocks.
  sigverify_rsa_key_t key_{};
};

class SigverifyInNonTestStates : public SigverifyInLcState {};

TEST_P(SigverifyInNonTestStates, BadOtpValue) {
  EXPECT_CALL(otp_,
              read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_USE_SW_RSA_VERIFY_OFFSET))
      .WillOnce(Return(0xA5A5A5A5));

  EXPECT_EQ(sigverify_rsa_verify(&kSignature, &key_, &kTestDigest, GetParam()),
            kErrorSigverifyBadOtpValue);
}

TEST_P(SigverifyInNonTestStates, GoodSignatureIbex) {
  EXPECT_CALL(otp_,
              read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_USE_SW_RSA_VERIFY_OFFSET))
      .WillOnce(Return(kHardenedBoolTrue));
  EXPECT_CALL(sigverify_mod_exp_ibex_, mod_exp(&key_, &kSignature, NotNull()))
      .WillOnce(DoAll(SetArgPointee<2>(kEncMsg), Return(kErrorOk)));

  EXPECT_EQ(sigverify_rsa_verify(&kSignature, &key_, &kTestDigest, GetParam()),
            kErrorOk);
}

TEST_P(SigverifyInNonTestStates, GoodSignatureOtbn) {
  EXPECT_CALL(otp_,
              read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_USE_SW_RSA_VERIFY_OFFSET))
      .WillOnce(Return(kHardenedBoolFalse));
  EXPECT_CALL(sigverify_mod_exp_otbn_, mod_exp(&key_, &kSignature, NotNull()))
      .WillOnce(DoAll(SetArgPointee<2>(kEncMsg), Return(kErrorOk)));

  EXPECT_EQ(sigverify_rsa_verify(&kSignature, &key_, &kTestDigest, GetParam()),
            kErrorOk);
}

TEST_P(SigverifyInNonTestStates, BadSignatureOtbn) {
  // Corrupt the words of the encoded message by flipping their bits and check
  // that signature verification fails.
  for (size_t i = 0; i < kSigVerifyRsaNumWords; ++i) {
    auto bad_enc_msg = kEncMsg;
    bad_enc_msg.data[i] = ~bad_enc_msg.data[i];

    EXPECT_CALL(otp_,
                read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_USE_SW_RSA_VERIFY_OFFSET))
        .WillOnce(Return(kHardenedBoolFalse));
    EXPECT_CALL(sigverify_mod_exp_otbn_, mod_exp(&key_, &kSignature, NotNull()))
        .WillOnce(DoAll(SetArgPointee<2>(bad_enc_msg), Return(kErrorOk)));

    EXPECT_EQ(
        sigverify_rsa_verify(&kSignature, &key_, &kTestDigest, GetParam()),
        kErrorSigverifyBadEncodedMessage);
  }
}

INSTANTIATE_TEST_SUITE_P(NonTestOperationalStates, SigverifyInNonTestStates,
                         testing::ValuesIn(kLcStatesNonTestOperational));

class SigverifyInTestStates : public SigverifyInLcState {};

TEST_P(SigverifyInTestStates, GoodSignatureIbex) {
  EXPECT_CALL(sigverify_mod_exp_ibex_, mod_exp(&key_, &kSignature, NotNull()))
      .WillOnce(DoAll(SetArgPointee<2>(kEncMsg), Return(kErrorOk)));

  EXPECT_EQ(sigverify_rsa_verify(&kSignature, &key_, &kTestDigest, GetParam()),
            kErrorOk);
}

TEST_P(SigverifyInTestStates, BadSignatureIbex) {
  // Corrupt the words of the encoded message by flipping their bits and check
  // that signature verification fails.
  for (size_t i = 0; i < kSigVerifyRsaNumWords; ++i) {
    auto bad_enc_msg = kEncMsg;
    bad_enc_msg.data[i] = ~bad_enc_msg.data[i];

    EXPECT_CALL(sigverify_mod_exp_ibex_, mod_exp(&key_, &kSignature, NotNull()))
        .WillOnce(DoAll(SetArgPointee<2>(bad_enc_msg), Return(kErrorOk)));

    EXPECT_EQ(
        sigverify_rsa_verify(&kSignature, &key_, &kTestDigest, GetParam()),
        kErrorSigverifyBadEncodedMessage);
  }
}

INSTANTIATE_TEST_SUITE_P(TestStates, SigverifyInTestStates,
                         testing::ValuesIn(kLcStatesTest));

class SigverifyInInvalidStates : public SigverifyInLcState {};

TEST_P(SigverifyInInvalidStates, BadLcState) {
  EXPECT_EQ(sigverify_rsa_verify(&kSignature, &key_, &kTestDigest, GetParam()),
            kErrorSigverifyBadLcState);
}

INSTANTIATE_TEST_SUITE_P(NonOperationalStates, SigverifyInInvalidStates,
                         testing::ValuesIn(kLcStatesNonOperational));

}  // namespace
}  // namespace sigverify_unittest
